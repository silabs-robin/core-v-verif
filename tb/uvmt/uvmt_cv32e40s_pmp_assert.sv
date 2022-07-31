module uvmt_cv32e40s_pmp_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import cv32e40s_rvfi_pkg::*;
  #(
    parameter int       PMP_GRANULARITY   = 0,
    parameter int       PMP_NUM_REGIONS   = 0,
    parameter int       IS_INSTR_SIDE     = 0,
    parameter mseccfg_t MSECCFG_RESET_VAL = MSECCFG_DEFAULT
  )
  (
   // Clock and Reset
   input logic        clk,
   input logic        rst_n,

   // Interface to CSRs
   input pmp_csr_t    csr_pmp_i,

   // Privilege mode
   input privlvl_t    priv_lvl_i,

   // Access checking
   input logic [33:0] pmp_req_addr_i,
   input pmp_req_e    pmp_req_type_i,
   input logic        pmp_req_err_o,

   // RVFI
   input logic        rvfi_valid,
   input logic [31:0] rvfi_insn,
   input logic [ 1:0] rvfi_mode,
   input rvfi_trap_t  rvfi_trap,
   input logic [PMP_MAX_REGIONS/4-1:0][31:0] rvfi_csr_pmpcfg_rdata,
   input logic [PMP_MAX_REGIONS-1:0]  [31:0] rvfi_csr_pmpaddr_rdata,
   input logic [31:0] rvfi_csr_mseccfg_rdata,
   input logic [31:0] rvfi_csr_mseccfgh_rdata,
   input logic [ 4:0] rvfi_rd_addr,
   input logic [31:0] rvfi_rd_wdata,
   input logic [ 4:0] rvfi_rs1_addr,
   input logic [31:0] rvfi_rs1_rdata
  );

  localparam logic [1:0] MODE_U = 2'b 00;
  localparam logic [1:0] MODE_M = 2'b 11;

  localparam logic [5:0] EXC_INSTR_ACC_FAULT    = 6'd 1;
  localparam logic [5:0] EXC_ILL_INSTR          = 6'd 2;
  localparam logic [5:0] EXC_INSTR_BUS_FAULT    = 6'd 48;
  localparam logic [5:0] EXC_INSTR_CHKSUM_FAULT = 6'd 49;

  localparam logic [2:0] DBG_TRIGGER = 3'd 2;

  localparam int NUM_CFG_REGS  = 16;
  localparam int NUM_ADDR_REGS = 64;

  localparam int CSRADDR_FIRST_PMPCFG  = 12'h 3A0;
  localparam int CSRADDR_FIRST_PMPADDR = 12'h 3B0;

  `define max(a,b) ((a) > (b) ? (a) : (b))

  typedef struct packed {
    logic r_mmode_r;
    logic r_mmode_lr;
    logic w_mmode_w;
    logic w_mmode_lw;
    logic x_mmode_x;
    logic x_mmode_lx;

    logic r_umode_r;
    logic w_umode_w;
    logic x_umode_x;

    logic r_umode_mml_w;
    logic r_umode_mml_wx;
    logic r_umode_mml_r;
    logic r_umode_mml_rx;
    logic r_umode_mml_rw;
    logic r_umode_mml_rwx;
    logic r_umode_mml_lrwx;

    logic r_mmode_mml_w;
    logic r_mmode_mml_wx;
    logic r_mmode_mml_lwx;
    logic r_mmode_mml_lr;
    logic r_mmode_mml_lrx;
    logic r_mmode_mml_lrw;
    logic r_mmode_mml_lrwx;

    logic w_umode_mml_wx;
    logic w_umode_mml_rw;
    logic w_umode_mml_rwx;

    logic w_mmode_mml_w;
    logic w_mmode_mml_wx;
    logic w_mmode_mml_lrw;

    logic x_mmode_mml_lx;
    logic x_mmode_mml_lw;
    logic x_mmode_mml_lwx;
    logic x_mmode_mml_lrx;

    logic x_umode_mml_x;
    logic x_umode_mml_rx;
    logic x_umode_mml_rwx;
    logic x_umode_mml_lw;
    logic x_umode_mml_lwx;

    logic r_mmode_nomatch_nommwp_r;
    logic w_mmode_nomatch_nommwp_w;
    logic x_mmode_nomatch_nommwp_x;
  } access_rsn_t;

  typedef struct {
    logic        is_matched;
    logic        is_locked;
    logic        is_any_locked;
    logic        is_rwx_ok;
    logic        is_access_allowed;
    logic        is_access_allowed_no_match;
    access_rsn_t val_access_allowed_reason;
    logic[$clog2(PMP_MAX_REGIONS)-1:0]  val_index;
  } match_status_t;

  match_status_t match_status;
  pmp_csr_t      pmp_csr_rvfi_rdata;

  default clocking @(posedge clk); endclocking
  default disable iff !(rst_n);


  // Check legal reasons to accept access

  always @* begin
    match_status = {<<{'0}};

    for (int region = 0; region < PMP_NUM_REGIONS; region++) begin
      match_status.is_any_locked = csr_pmp_i.cfg[region].lock ? 1'b1 : match_status.is_any_locked;
    end

    for (int region = 0; region < PMP_NUM_REGIONS; region++) begin
      if (is_match_na4(region) || is_match_tor(region) || is_match_napot(region)) begin
        match_status.val_index  = region;
        match_status.is_matched = 1'b1;
        break;
      end
    end

    // Allowed access whitelist table
    if (match_status.is_matched) begin
      match_status.is_locked = csr_pmp_i.cfg[match_status.val_index].lock;
      if (csr_pmp_i.mseccfg.mml === 1'b1) begin
        case (pmp_req_type_i)
          PMP_ACC_READ: begin
            // ------------------------------------------------------------
            // Read access U-Mode
            // ------------------------------------------------------------
            // Read access U-mode - Shared data region, U-mode RO
            match_status.val_access_allowed_reason.r_umode_mml_w    = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Read access U-mode - Shared data region, U-mode RW
            match_status.val_access_allowed_reason.r_umode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Read access U-mode - Read flag
            match_status.val_access_allowed_reason.r_umode_mml_r    = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Read access U-mode - Read/execute flag
            match_status.val_access_allowed_reason.r_umode_mml_rx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Read access U-mode - Read/Write flag
            match_status.val_access_allowed_reason.r_umode_mml_rw   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Read access U-mode - Read/Write/Execute flag
            match_status.val_access_allowed_reason.r_umode_mml_rwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Read access U-mode - Locked shared region
            match_status.val_access_allowed_reason.r_umode_mml_lrwx = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );

            // ------------------------------------------------------------
            // Read access M-Mode
            // ------------------------------------------------------------
            // Read access M-mode - Shared data region, U-mode RO
            match_status.val_access_allowed_reason.r_mmode_mml_w    = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Read access M-mode - Shared data region, U-mode RW
            match_status.val_access_allowed_reason.r_mmode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Read access M-mode - Shared code region, M-mode RX
            match_status.val_access_allowed_reason.r_mmode_mml_lwx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Read access M-mode - Locked/Read
            match_status.val_access_allowed_reason.r_mmode_mml_lr   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Read access M-mode - Locked read/execute region
            match_status.val_access_allowed_reason.r_mmode_mml_lrx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Read access M-mode - Locked read/write region
            match_status.val_access_allowed_reason.r_mmode_mml_lrw  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Read access M-mode - Locked shared region
            match_status.val_access_allowed_reason.r_mmode_mml_lrwx = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
          end // PMP_ACC_READ

          PMP_ACC_WRITE: begin
            // ------------------------------------------------------------
            // Write access U-Mode
            // ------------------------------------------------------------
            // Write access U-mode - Shared data region, U-mode RW
            match_status.val_access_allowed_reason.w_umode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Write access U-mode - Read/write region
            match_status.val_access_allowed_reason.w_umode_mml_rw   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Write access U-mode - Read/write/execute region
            match_status.val_access_allowed_reason.w_umode_mml_rwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );

            // ------------------------------------------------------------
            // Write access M-Mode
            // ------------------------------------------------------------
            // Write access M-mode - Shared data region, U-mode RO
            match_status.val_access_allowed_reason.w_mmode_mml_w    = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Write access M-mode - Shared data region, U-mode RW
            match_status.val_access_allowed_reason.w_mmode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Write access M-mode - Locked read/write region
            match_status.val_access_allowed_reason.w_mmode_mml_lrw  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
          end // PMP_ACC_WRITE

          PMP_ACC_EXEC: begin
            // ------------------------------------------------------------
            // Execute access U-Mode
            // ------------------------------------------------------------
            // Execute access U-mode - Executable region
            match_status.val_access_allowed_reason.x_umode_mml_x    = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Execute access U-mode - Read/execute region
            match_status.val_access_allowed_reason.x_umode_mml_rx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Execute access U-mode - Read/write/execute region
            match_status.val_access_allowed_reason.x_umode_mml_rwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Execute access U-mode - Locked shared code region, X only
            match_status.val_access_allowed_reason.x_umode_mml_lw   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Execute access U-mode - Locked shared code region, M-mode RX
            match_status.val_access_allowed_reason.x_umode_mml_lwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );

            // ------------------------------------------------------------
            // Execute access M-Mode
            // ------------------------------------------------------------
            // Execute access M-mode - Locked executable region
            match_status.val_access_allowed_reason.x_mmode_mml_lx   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Execute access M-mode - Locked shared code region, X-only
            match_status.val_access_allowed_reason.x_mmode_mml_lw   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b0
            );
            // Execute access M-mode - Locked shared code region, M-mode RX
            match_status.val_access_allowed_reason.x_mmode_mml_lwx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
            // Execute access M-mode - Locked Read/Execute region
            match_status.val_access_allowed_reason.x_mmode_mml_lrx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status.val_index].exec  == 1'b1
            );
          end // PMP_ACC_EXEC
        endcase // case(pmp_req_type_i)

        end else begin // mmwp low
          case ( priv_lvl_i )
            PRIV_LVL_M:
              case ( {pmp_req_type_i, match_status.is_locked} )
                { PMP_ACC_READ,  1'b1 }: match_status.val_access_allowed_reason.r_mmode_lr = csr_pmp_i.cfg[match_status.val_index].read;
                { PMP_ACC_READ,  1'b0 }: match_status.val_access_allowed_reason.r_mmode_r  = 1'b1;
                { PMP_ACC_WRITE, 1'b1 }: match_status.val_access_allowed_reason.w_mmode_lw = csr_pmp_i.cfg[match_status.val_index].write;
                { PMP_ACC_WRITE, 1'b0 }: match_status.val_access_allowed_reason.w_mmode_w  = 1'b1;
                { PMP_ACC_EXEC,  1'b1 }: match_status.val_access_allowed_reason.x_mmode_lx = csr_pmp_i.cfg[match_status.val_index].exec;
                { PMP_ACC_EXEC,  1'b0 }: match_status.val_access_allowed_reason.x_mmode_x  = 1'b1;
              endcase
            PRIV_LVL_U:
              case ( pmp_req_type_i )
                PMP_ACC_READ:  match_status.val_access_allowed_reason.r_umode_r = csr_pmp_i.cfg[match_status.val_index].read;
                PMP_ACC_WRITE: match_status.val_access_allowed_reason.w_umode_w = csr_pmp_i.cfg[match_status.val_index].write;
                PMP_ACC_EXEC:  match_status.val_access_allowed_reason.x_umode_x = csr_pmp_i.cfg[match_status.val_index].exec;
              endcase
          endcase // case (priv_lvl_i)

        end
      match_status.is_rwx_ok = |match_status.val_access_allowed_reason;

      end else begin
        // ------------------------------------------------------------
        // NO MATCH REGION
        // ------------------------------------------------------------
        // No matching region found, allow only M-access, and only if MMWP bit is not set
        case ( {pmp_req_type_i, priv_lvl_i} )
          { PMP_ACC_READ,  PRIV_LVL_M }:
            match_status.val_access_allowed_reason.r_mmode_nomatch_nommwp_r = !csr_pmp_i.mseccfg.mmwp;
          { PMP_ACC_WRITE, PRIV_LVL_M }:
            match_status.val_access_allowed_reason.w_mmode_nomatch_nommwp_w = !csr_pmp_i.mseccfg.mmwp;
          { PMP_ACC_EXEC,  PRIV_LVL_M }:
            match_status.val_access_allowed_reason.x_mmode_nomatch_nommwp_x = !csr_pmp_i.mseccfg.mmwp && !csr_pmp_i.mseccfg.mml;
        endcase
        match_status.is_access_allowed_no_match = |match_status.val_access_allowed_reason;
      end
      // Access is allowed if any one of the above conditions matches
      match_status.is_access_allowed = |match_status.val_access_allowed_reason;
    end



  // Helper functions
  function automatic int is_match_na4(input logic[$clog2(PMP_MAX_REGIONS)-1:0] region);
    is_match_na4 = (csr_pmp_i.cfg[region].mode   == PMP_MODE_NA4)  &&
                   (csr_pmp_i.addr[region][33:2] == pmp_req_addr_i[33:2]);
  endfunction : is_match_na4

  function automatic logic is_match_tor(input logic[$clog2(PMP_MAX_REGIONS)-1:0] region);
    logic [33:2+PMP_GRANULARITY] req, hi, lo;

    req  = pmp_req_addr_i[33:2+PMP_GRANULARITY];
    hi   = csr_pmp_i.addr[region][33:2+PMP_GRANULARITY];
    lo   = (region > 0) ? csr_pmp_i.addr[region - 1'b1][33:2+PMP_GRANULARITY] : 0;

    is_match_tor = (csr_pmp_i.cfg[region].mode == PMP_MODE_TOR) &&
                   (lo   <= req) &&
                   (req   < hi);

  endfunction : is_match_tor

  function automatic int is_match_napot(input logic[$clog2(PMP_MAX_REGIONS)-1:0] region);
    logic [31:0] mask = gen_mask(region);
    logic [31:0] csr_addr_masked = csr_pmp_i.addr[region][33:2] & mask;
    logic [31:0] req_addr_masked = pmp_req_addr_i[33:2] & mask;

    is_match_napot = (csr_pmp_i.cfg[region].mode == PMP_MODE_NAPOT) &&
                     (csr_addr_masked == req_addr_masked);

  endfunction : is_match_napot

  function automatic logic[31:0] gen_mask(input logic[$clog2(PMP_MAX_REGIONS)-1:0] i);
    logic [31:0] mask;
    logic [31:0] csr_addr;

    mask = '1;
    if (PMP_GRANULARITY >= 1) begin
      mask[`max(PMP_GRANULARITY-1, 0) : 0] = '0;  // TODO remove or assume+assert?
    end

    csr_addr = csr_pmp_i.addr[i][33:2];
    if (PMP_GRANULARITY >= 2) begin
      csr_addr[`max(PMP_GRANULARITY-2, 0) : 0] = '1;  // TODO should be assumed+assert?
    end

    for (int j = 0; j < 32; j++) begin
      mask[j] = 0;
      if (csr_addr[j] == 0) begin
        break;
      end
    end

    return mask;
  endfunction


  // Extra covers and asserts to comprehensively match the spec

  // Cover the helper-RTL internals
  generate
    if (IS_INSTR_SIDE === 1'b1 && PMP_NUM_REGIONS > 0) begin : gen_cp_instr_side
      covergroup cg_internals_instr_side @(posedge clk);
        // Machine mode execute accesses
        cp_x_mmode_x                : coverpoint match_status.val_access_allowed_reason.x_mmode_x                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_lx               : coverpoint match_status.val_access_allowed_reason.x_mmode_lx               { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lx           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lrx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_nomatch_nommwp_x : coverpoint match_status.val_access_allowed_reason.x_mmode_nomatch_nommwp_x { bins low  = {1'b0}; bins high = {1'b1}; }
        // User mode execute accesses
        cp_x_umode_x                : coverpoint match_status.val_access_allowed_reason.x_umode_x                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_x            : coverpoint match_status.val_access_allowed_reason.x_umode_mml_x            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        // Ignore bins for unreachable load/stores on instruction if
        // Machine mode l/s accesses
        cp_r_mmode_nomatch_nommwp_r : coverpoint match_status.val_access_allowed_reason.r_mmode_nomatch_nommwp_r { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_nomatch_nommwp_w : coverpoint match_status.val_access_allowed_reason.w_mmode_nomatch_nommwp_w { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_w            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_lrw          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_r                : coverpoint match_status.val_access_allowed_reason.r_mmode_r                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_lr               : coverpoint match_status.val_access_allowed_reason.r_mmode_lr               { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_w                : coverpoint match_status.val_access_allowed_reason.w_mmode_w                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_lw               : coverpoint match_status.val_access_allowed_reason.w_mmode_lw               { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_w            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lr           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lr           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrw          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrwx         { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // User mode l/s accesses
        cp_w_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_r                : coverpoint match_status.val_access_allowed_reason.r_umode_r                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_umode_w                : coverpoint match_status.val_access_allowed_reason.w_umode_w                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_w            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_r            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_r            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_umode_mml_lrwx         { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
      endgroup : cg_internals_instr_side
      cg_internals_instr_side cg_instr = new();
    end
    else if (IS_INSTR_SIDE === 1'b0 && PMP_NUM_REGIONS > 0) begin : gen_cp_data_side
      covergroup cg_internals_data_side @(posedge clk);
        // Ignore bins for unreachable execute accesses on lsu if
        // Machine mode execute accesses
        cp_x_mmode_x                : coverpoint match_status.val_access_allowed_reason.x_mmode_x                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_lx               : coverpoint match_status.val_access_allowed_reason.x_mmode_lx               { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lx           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lrx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_nomatch_nommwp_x : coverpoint match_status.val_access_allowed_reason.x_mmode_nomatch_nommwp_x { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // User mode execute accesses
        cp_x_umode_x                : coverpoint match_status.val_access_allowed_reason.x_umode_x                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_x            : coverpoint match_status.val_access_allowed_reason.x_umode_mml_x            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // Machine mode l/s accesses
        cp_r_mmode_nomatch_nommwp_r : coverpoint match_status.val_access_allowed_reason.r_mmode_nomatch_nommwp_r { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_nomatch_nommwp_w : coverpoint match_status.val_access_allowed_reason.w_mmode_nomatch_nommwp_w { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_w            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_lrw          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_r                : coverpoint match_status.val_access_allowed_reason.r_mmode_r                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_lr               : coverpoint match_status.val_access_allowed_reason.r_mmode_lr               { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_w                : coverpoint match_status.val_access_allowed_reason.w_mmode_w                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_lw               : coverpoint match_status.val_access_allowed_reason.w_mmode_lw               { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_w            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lr           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lr           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrw          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrwx         { bins low  = {1'b0}; bins high = {1'b1}; }
        // User mode l/s accesses
        cp_w_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_r                : coverpoint match_status.val_access_allowed_reason.r_umode_r                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_umode_w                : coverpoint match_status.val_access_allowed_reason.w_umode_w                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_w            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_r            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_r            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_umode_mml_lrwx         { bins low  = {1'b0}; bins high = {1'b1}; }
      endgroup : cg_internals_data_side
      cg_internals_data_side cg_instr = new();
    end
  endgenerate

  generate
    if (PMP_NUM_REGIONS > 0) begin : gen_cg_common
      covergroup cg_internals_common @(posedge clk);
        cp_ismatch_tor:   coverpoint is_match_tor(match_status.val_index) iff (match_status.is_matched);

        cp_napot_min_8byte: coverpoint { pmp_req_addr_i[2], csr_pmp_i.addr[match_status.val_index][2] }
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched         == 1'b1 &&
               match_status.is_access_allowed  == 1'b1
        );

        cp_napot_min_8byte_disallowed: coverpoint { pmp_req_addr_i[2], csr_pmp_i.addr[match_status.val_index][2] }
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched         == 1'b1 &&
               match_status.is_access_allowed  == 1'b0
        );

        cp_napot_encoding: coverpoint ( pmp_req_addr_i[33:2+PMP_GRANULARITY] == csr_pmp_i.addr[match_status.val_index][33:2+PMP_GRANULARITY] )
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched        == 1'b1 &&
               match_status.is_access_allowed == 1'b1
        );

        cp_napot_encoding_disallowed: coverpoint ( pmp_req_addr_i[33:2+PMP_GRANULARITY] == csr_pmp_i.addr[match_status.val_index][33:2+PMP_GRANULARITY] )
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched        == 1'b1 &&
               match_status.is_access_allowed == 1'b0
        );

      endgroup
      cg_internals_common cg_int = new();
    end
  endgenerate

  // NA4 only available in G=1
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_na4onlyg0
    a_na4_only_g0: assert property (
      (csr_pmp_i.cfg[region].mode == PMP_MODE_NA4)
      |->
      (PMP_GRANULARITY === 1'b 0)
    );

    a_na4_not_when_g: assert property (
      // "Redundant" assert for (antecedent) coverage
      (PMP_GRANULARITY !== 1'b 0)
      |->
      (csr_pmp_i.cfg[region].mode !== PMP_MODE_NA4)
    );
  end endgenerate

  // NA4 has 4-byte granularity
  generate if (PMP_GRANULARITY == 0 && PMP_NUM_REGIONS > 0) begin: gen_na4is4byte
    a_na4_is_4byte: assert property (
        csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NA4 &&
        match_status.is_matched        == 1'b1 &&
        match_status.is_access_allowed == 1 |->
           pmp_req_addr_i[31:2] == csr_pmp_i.addr[match_status.val_index][31:2]
    );
  end endgenerate

  // Spec: "The combination R=0 and W=1 is reserved for future use" - Exception: mml set
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rwfuture
    a_rw_futureuse: assert property  (
      csr_pmp_i.mseccfg.mml === 1'b0 |->
        !(csr_pmp_i.cfg[region].read == 0 && csr_pmp_i.cfg[region].write == 1)
    );
  end endgenerate

  // mseccfg.RLB = 1 LOCKED rules may be modified/removed, LOCKED entries may be modified -> test inverse
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rlb_locked
    a_norlb_locked_rules_cannot_modify : assert property (
      csr_pmp_i.mseccfg.rlb === 1'b0 && csr_pmp_i.cfg[region].lock === 1'b1 |=>
        $stable(csr_pmp_i.cfg[region])
    );
  end endgenerate

  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rlb_locked_cov
    c_rlb_locked_rules_can_modify_addr : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.addr[region])
    );

    c_rlb_locked_rules_can_modify_lock : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].lock)
    );

    c_rlb_locked_rules_can_modify_exec : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].exec)
    );

    c_rlb_locked_rules_can_modify_mode : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].mode)
    );

    c_rlb_locked_rules_can_modify_write : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].write)
    );

    c_rlb_locked_rules_can_modify_read : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].read)
    );

    c_rlb_locked_rules_can_remove : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 &&
      csr_pmp_i.cfg[region].lock == 1'b1 &&
      csr_pmp_i.cfg[region].mode != PMP_MODE_OFF ##1
        csr_pmp_i.cfg[region].mode === PMP_MODE_OFF
    );

    // Adding an M-mode-only or a locked Shared-Region rule with executable privileges is not possible and
    // such pmpcfg writes are ignored, leaving pmpcfg unchanged. This restriction can be temporarily lifted
    // e.g. during the boot process, by setting mseccfg.RLB.
    a_mmode_only_or_shared_executable_ignore: assert property (
      csr_pmp_i.mseccfg.mml === 1'b1 && csr_pmp_i.mseccfg.rlb === 1'b0 |=>
        $stable(csr_pmp_i.cfg[region])
      or
        not ($changed(csr_pmp_i.cfg[region]) ##0
        csr_pmp_i.cfg[region].lock === 1'b1 ##0
        csr_pmp_i.cfg[region].read === 1'b0 ##0
        csr_pmp_i.cfg[region].write || csr_pmp_i.cfg[region].exec)
    );

    c_mmode_only_or_shared_executable: cover property (
      csr_pmp_i.mseccfg.mml === 1'b1 && csr_pmp_i.mseccfg.rlb === 1'b1
      ##1
        $changed(csr_pmp_i.cfg[region])     ##0
        csr_pmp_i.cfg[region].lock === 1'b1 ##0
        csr_pmp_i.cfg[region].read === 1'b0 ##0
        csr_pmp_i.cfg[region].write || csr_pmp_i.cfg[region].exec
    );
  end endgenerate

  // Validate PMP mode settings
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_matchmode
    a_matchmode: assert property (
      csr_pmp_i.cfg[region].mode inside {
        PMP_MODE_OFF,
        PMP_MODE_TOR,
        PMP_MODE_NA4,
        PMP_MODE_NAPOT
      }
    );
  end endgenerate

  generate if (PMP_NUM_REGIONS > 0) begin : gen_pmp_assert
    // Check output vs model
    a_accept_only_legal : assert property (
      (pmp_req_err_o === 1'b0) |-> match_status.is_access_allowed
    );

    a_deny_only_illegal : assert property (
      pmp_req_err_o |-> (match_status.is_access_allowed === 1'b0)
    );

    // Assert that only one (or none) valid access reason can exist for any given access
    a_unique_access_allowed_reason: assert property (
      $countones(match_status.val_access_allowed_reason) <= 1
    );

    // Validate privilege level
    a_privmode: assert property (
      priv_lvl_i inside {
        PRIV_LVL_M,
        PRIV_LVL_U
      }
    );

    // Validate access type
    a_req_type: assert property (
      pmp_req_type_i inside {
        PMP_ACC_READ,
        PMP_ACC_WRITE,
        PMP_ACC_EXEC
      }
    );
    // SMEPMP 2b: When mseccfg.RLB is 0 and pmpcfg.L is 1 in any rule or entry (including disabled entries), then
    // mseccfg.RLB remains 0 and any further modifications to mseccfg.RLB are ignored until a PMP reset.
    //
    // In other words: mseccfg.RLB = 0 and pmpcfg.L = 1 in any rule or entry (including disabled),
    // mseccfg.RLB remains 0 and does not change until PMP reset
    a_rlb_never_fall_while_locked: assert property (
      csr_pmp_i.mseccfg.rlb === 1'b0 && match_status.is_any_locked |=>
        $stable(csr_pmp_i.mseccfg.rlb)
    );

    // SMEPMP 3: On mseccfg we introduce a field in bit 1 called Machine Mode Whitelist Policy (mseccfg.MMWP).
    // This is a sticky bit, meaning that once set it cannot be unset until a PMP reset.
    a_mmwp_never_fall_until_reset: assert property (
      csr_pmp_i.mseccfg.mmwp === 1'b1 |=>
        $stable(csr_pmp_i.mseccfg.mmwp)
    );

    // SMEPMP 4: On mseccfg we introduce a field in bit 0 called Machine Mode Lockdown (mseccfg.MML). This is a
    // sticky bit, meaning that once set it cannot be unset until a PMP reset.
    a_mml_never_fall_until_reset: assert property (
      csr_pmp_i.mseccfg.mml === 1'b1 |=>
        $stable(csr_pmp_i.mseccfg.mml)
    );

    // U-mode fails if no match
    a_nomatch_umode_fails: assert property (
      priv_lvl_i == PRIV_LVL_U && match_status.is_matched == 1'b0 |->
        pmp_req_err_o
    );

    // U-mode or L=1 succeed only if RWX
    a_uorl_onlyif_rwx: assert property (
      ( priv_lvl_i == PRIV_LVL_U || match_status.is_matched == 1'b1 ) && !pmp_req_err_o |->
        match_status.is_rwx_ok
    );

    // After a match, LRWX determines access
    a_lrwx_aftermatch: assert property (
      match_status.is_matched == 1'b1 && !pmp_req_err_o |->
        match_status.is_rwx_ok
    );

    // SMEPMP 1: The reset value of mseccfg is implementation-specific, otherwise if backwards
    // compatibility is a requirement it should reset to zero on hard reset.
    a_mseccfg_reset_val: assert property (
      $rose(rst_n) |-> csr_pmp_i.mseccfg === MSECCFG_RESET_VAL
    );
  end endgenerate


  // RVFI

  // Helper signals
  wire  is_rvfi_csr_instr =
    rvfi_valid  &&
    (rvfi_insn[6:0] == 7'b 1110011)  &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7});
  wire  is_rvfi_exception =
    rvfi_valid  &&
    rvfi_trap.trap  &&
    rvfi_trap.exception;
  wire  is_rvfi_exc_ill_instr =
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_ILL_INSTR);
  wire  is_rvfi_exc_instr_acc_fault =
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_INSTR_ACC_FAULT);
  wire  is_rvfi_exc_instr_bus_fault=
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_INSTR_BUS_FAULT);
  wire  is_rvfi_exc_instr_chksum_fault=
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_INSTR_CHKSUM_FAULT);
  wire  is_rvfi_dbg_trigger =
    rvfi_valid  &&
    rvfi_trap.debug  &&
    (rvfi_trap.debug_cause == DBG_TRIGGER);
  wire  is_rvfi_csr_read_instr =
    is_rvfi_csr_instr  &&
    rvfi_rd_addr;
  wire  is_rvfi_csr_write_instr =
    is_rvfi_csr_instr  &&
    rvfi_rs1_addr  &&
    !((rvfi_insn[14:12] inside {3'b 010, 3'b 011}) && !rvfi_rs1_rdata);  // CSRRS/C wo/ high bits

  for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin: gen_pmp_csr_readout
    localparam pmpcfg_reg_i    = i / 4;
    localparam pmpcfg_field_hi = (8 * (i % 4)) + 7;
    localparam pmpcfg_field_lo = (8 * (i % 4));

    assign pmp_csr_rvfi_rdata.cfg[i]  = rvfi_csr_pmpcfg_rdata[pmpcfg_reg_i][pmpcfg_field_hi : pmpcfg_field_lo];
    assign pmp_csr_rvfi_rdata.addr[i] = rvfi_csr_pmpaddr_rdata[i];  // TODO:ropeders is this assignment correct?
  end
  assign pmp_csr_rvfi_rdata.mseccfg = {rvfi_csr_mseccfgh_rdata, rvfi_csr_mseccfg_rdata};

  // PMP CSRs only accessible from M-mode
  property p_csrs_mmode_only;
    is_rvfi_csr_instr  &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_insn[31:20] inside {['h3A0 : 'h3EF], 'h747, 'h757})
    |->
    is_rvfi_exc_ill_instr  ^
    is_rvfi_exc_instr_acc_fault  ^
    is_rvfi_dbg_trigger ^
    is_rvfi_exc_instr_bus_fault  ^
    is_rvfi_exc_instr_chksum_fault;
  endproperty : p_csrs_mmode_only
  a_csrs_mmode_only: assert property (
    p_csrs_mmode_only
  );
  cov_csrs_mmod_only: cover property (
    p_csrs_mmode_only  and  is_rvfi_exc_ill_instr
  );

  // NAPOT, some bits read as ones, depending on G
  if (PMP_GRANULARITY >= 2) begin: gen_napot_ones_g2
    //TODO:ropeders no magic numbers
    for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_napot_ones_i
      a_napot_ones: assert property (
        rvfi_valid  &&
        pmp_csr_rvfi_rdata.cfg[i].mode[1]
        |->
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY-2:0] == '1)
      );
    end
  end

  // OFF/TOR, some bits read as zeros, depending on G
  if (PMP_GRANULARITY >= 1) begin: gen_all_zeros_g1
    for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_all_zeros_i
      a_all_zeros: assert property (
        rvfi_valid  &&
        (pmp_csr_rvfi_rdata.cfg[i].mode[1] === 1'b 0)
        |->
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY-1:0] == '0)
      );
    end
  end

  // Software-view on PMP CSRs matches RVFI-view
  for (genvar i = 0; i < NUM_CFG_REGS; i++) begin: gen_swview_cfg
    a_pmpcfg_swview: assert property (
      // TODO:ropeders no magic numbers
      is_rvfi_csr_read_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPCFG + i))
      |->
      (rvfi_rd_wdata == rvfi_csr_pmpcfg_rdata[i])
    );
  end
  for (genvar i = 0; i < NUM_ADDR_REGS; i++) begin: gen_swview_addr
    a_pmpaddr_swview: assert property (
      // TODO:ropeders no magic numbers
      is_rvfi_csr_read_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))
      |->
      (rvfi_rd_wdata == rvfi_csr_pmpaddr_rdata[i])
    );
  end

  // Software views does not change underlying register value
  property p_storage_unaffected(i);
    logic [31:0] pmpaddr;
    accept_on (
      is_rvfi_csr_write_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))
    )
      rvfi_valid  ##0
      pmp_csr_rvfi_rdata.cfg[i].mode[1]  ##0
      (1, pmpaddr = pmp_csr_rvfi_rdata.addr[i])
      ##1
      (rvfi_valid [->1])  ##0
      (pmp_csr_rvfi_rdata.cfg[i].mode[1] == 1'b 0)
      ##1
      (rvfi_valid [->1])  ##0
      pmp_csr_rvfi_rdata.cfg[i].mode[1]
    |->
    (pmp_csr_rvfi_rdata.addr[i][31:0] == pmpaddr);
    // Note, this _can_ be generalized more, but at a complexity/readability cost
  endproperty : p_storage_unaffected
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_storage_unaffected
    a_storage_unaffected: assert property (
      p_storage_unaffected(i)
    );
  end

  // TODO:ropeders "uvm_error" on all assertions

  // Software-view can read the granularity level
  a_granularity_determination: assert property (
    (is_rvfi_csr_instr && (rvfi_insn[14:12] == 3'b 001)) &&  // CSRRW instr,
    (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + 0))    &&  // to a "pmpaddr" CSR,
    ((rvfi_rs1_rdata == '1) && rvfi_rs1_addr)            &&  // writing all ones.
    (pmp_csr_rvfi_rdata.cfg[0] == '0)                    &&  // Related cfg is 0,
    (pmp_csr_rvfi_rdata.cfg[0+1] == '0)                  &&  // above cfg is 0.
    !rvfi_trap                                               // (Trap doesn't meddle.)
    |=>
    (rvfi_valid [->1])  ##0
    (rvfi_csr_pmpaddr_rdata[0][31:PMP_GRANULARITY] == '1)  &&
    (rvfi_csr_pmpaddr_rdata[0][PMP_GRANULARITY-1:0] == '0)
    // Note: _Can_ be generalized for all i
  );

  // Locking is forever
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_until_reset
    a_until_reset: assert property (
      pmp_csr_rvfi_rdata.cfg[i].lock  &&
      !pmp_csr_rvfi_rdata.mseccfg.rlb
      |->
      always pmp_csr_rvfi_rdata.cfg[i].lock
    );
  end

  // Locked entries, ignore pmpicfg/pmpaddri writes
  a_ignore_writes_notrap: assert property (
    is_rvfi_csr_write_instr  &&
    (rvfi_insn[31:20] inside {(CSRADDR_FIRST_PMPADDR + 0), (CSRADDR_FIRST_PMPCFG + 0)})  &&
    (pmp_csr_rvfi_rdata.cfg[0].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
    (rvfi_mode == MODE_M)
    |->
    (rvfi_trap.exception_cause != EXC_ILL_INSTR)
  );
  a_ignore_writes_nochange: assert property (
    rvfi_valid &&
    (pmp_csr_rvfi_rdata.cfg[0].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)
    |=>
    always (
      !$changed(pmp_csr_rvfi_rdata.cfg[0])  &&
      !$changed(pmp_csr_rvfi_rdata.addr[0])
    )
  );
  // Note, can be easily checked for all i

  // Locked TOR, ignore i-1 addr writes
  for (genvar i = 1; i < PMP_NUM_REGIONS; i++) begin: gen_ignore_tor
    a_ignore_tor: assert property (
      rvfi_valid &&
      (pmp_csr_rvfi_rdata.cfg[i].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
      (pmp_csr_rvfi_rdata.cfg[i].mode == PMP_MODE_TOR)
      |=>
      always !$changed(pmp_csr_rvfi_rdata.addr[i-1][31:PMP_GRANULARITY])
    );
  end

endmodule : uvmt_cv32e40s_pmp_assert
