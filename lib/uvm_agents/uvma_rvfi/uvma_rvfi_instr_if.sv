// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


`ifndef __UVMA_RVFI_INSTR_IF_SV__
`define __UVMA_RVFI_INSTR_IF_SV__

/**
 * Encapsulates all signals and clocking of RVFI Instruction interface. Used by
 * monitor,
 */
interface uvma_rvfi_instr_if_t
  import uvma_rvfi_pkg::*;
  #(int ILEN=DEFAULT_ILEN,
    int XLEN=DEFAULT_XLEN)
  (
    input logic                      clk,
    input logic                      reset_n,

    input logic                      rvfi_valid,
    input logic [ORDER_WL-1:0]       rvfi_order,
    input logic [ILEN-1:0]           rvfi_insn,
    input rvfi_trap_t                rvfi_trap,
    input logic                      rvfi_halt,
    input logic [RVFI_DBG_WL-1:0]    rvfi_dbg,
    input logic                      rvfi_dbg_mode,
    input logic [RVFI_NMIP_WL-1:0]   rvfi_nmip,
    input rvfi_intr_t                rvfi_intr,
    input logic [MODE_WL-1:0]        rvfi_mode,
    input logic [IXL_WL-1:0]         rvfi_ixl,
    input logic [XLEN-1:0]           rvfi_pc_rdata,
    input logic [XLEN-1:0]           rvfi_pc_wdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rs1_addr,
    input logic [XLEN-1:0]           rvfi_rs1_rdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rs2_addr,
    input logic [XLEN-1:0]           rvfi_rs2_rdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rs3_addr,
    input logic [XLEN-1:0]           rvfi_rs3_rdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rd1_addr,
    input logic [XLEN-1:0]           rvfi_rd1_wdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rd2_addr,
    input logic [XLEN-1:0]           rvfi_rd2_wdata,

    input logic [(32*XLEN)-1:0]      rvfi_gpr_rdata,
    input logic [(32)-1:0]           rvfi_gpr_rmask,
    input logic [(32*XLEN)-1:0]      rvfi_gpr_wdata,
    input logic [(32)-1:0]           rvfi_gpr_wmask,

    input logic [(NMEM*XLEN)-1:0]    rvfi_mem_addr,
    input logic [(NMEM*XLEN)-1:0]    rvfi_mem_rdata,
    input logic [(NMEM*XLEN/8)-1:0]  rvfi_mem_rmask,
    input logic [(NMEM*XLEN)-1:0]    rvfi_mem_wdata,
    input logic [(NMEM*XLEN/8)-1:0]  rvfi_mem_wmask,

    input logic [2:0]                instr_prot,
    input logic [NMEM*3-1:0]         mem_prot
  );

  // -------------------------------------------------------------------
  // Local param
  // -------------------------------------------------------------------
  //instruction (rvfi_instr) masks
  localparam INSTR_MASK_FULL        = 32'h FFFF_FFFF;
  localparam INSTR_MASK_R_TYPE      = 32'h FE00_707F;
  localparam INSTR_MASK_I_S_B_TYPE  = 32'h 0000_707F;
  localparam INSTR_MASK_U_J_TYPE    = 32'h 0000_007F;
  localparam INSTR_MASK_CSRADDR     = 32'h FFF0_0000;
  localparam INSTR_MASK_CSRUIMM     = 32'h 000F_8000;
  localparam INSTR_MASK_CMPR        = 32'h 0000_E003;

  //instruction (rvfi_instr) comparison values
  localparam INSTR_OPCODE_DRET      = 32'h 7B20_0073;
  localparam INSTR_OPCODE_MRET      = 32'h 3020_0073;
  localparam INSTR_OPCODE_URET      = 32'h 0020_0073;
  localparam INSTR_OPCODE_WFI       = 32'h 1050_0073;
  localparam INSTR_OPCODE_WFE       = 32'h 8C00_0073;
  localparam INSTR_OPCODE_EBREAK    = 32'h 0010_0073;
  localparam INSTR_OPCODE_C_EBREAK  = 32'h 0000_9002;
  localparam INSTR_OPCODE_ECALL     = 32'h 0000_0073;
  localparam INSTR_OPCODE_CSLLI     = 32'h 0000_0002;

  localparam INSTR_OPCODE_CSRRW     = 32'h 0000_1073;
  localparam INSTR_OPCODE_CSRRS     = 32'h 0000_2073;
  localparam INSTR_OPCODE_CSRRC     = 32'h 0000_3073;
  localparam INSTR_OPCODE_CSRRWI    = 32'h 0000_5073;
  localparam INSTR_OPCODE_CSRRSI    = 32'h 0000_6073;
  localparam INSTR_OPCODE_CSRRCI    = 32'h 0000_7073;

  localparam INSTR_MASK_PUSHPOP   = 32'b 11111111_11111111_111_11111_0000_00_11;
  localparam INSTR_OPCODE_PUSH    = 32'b 00000000_00000000_101_11000_0000_00_10;
  localparam INSTR_OPCODE_POP     = 32'b 00000000_00000000_101_11010_0000_00_10;
  localparam INSTR_OPCODE_POPRET  = 32'b 00000000_00000000_101_11110_0000_00_10;
  localparam INSTR_OPCODE_POPRETZ = 32'b 00000000_00000000_101_11100_0000_00_10;

  localparam INSTR_MASK_TABLEJUMP   = 32'b 11111111_11111111_111_111_00000000_11;
  localparam INSTR_OPCODE_TABLEJUMP = 32'b 00000000_00000000_101_000_00000000_10;

  localparam INSTR_MASK_FENCE    = 32'b 00000000000000000_111_00000_1111111;
  localparam INSTR_OPCODE_FENCE  = 32'b 00000000000000000_000_00000_0001111;
  localparam INSTR_MASK_FENCEI   = 32'b 00000000000000000_111_00000_1111111;
  localparam INSTR_OPCODE_FENCEI = 32'b 00000000000000000_001_00000_0001111;

  //positions
  localparam int INSTR_CSRADDR_POS  = 20;
  localparam int INSTR_CSRUIMM_POS  = 15;


  localparam INTR_CAUSE_NMI_MASK    = 11'h 400;




  // -------------------------------------------------------------------
  // Local variables
  // -------------------------------------------------------------------
  bit   [CYCLE_CNT_WL-1:0]          cycle_cnt = 0;
  int unsigned                      nmi_instr_cnt = 0;

  logic [(32)-1:0][XLEN-1:0]        gpr_rdata_array;
  logic [(32)-1:0]                  gpr_rmask_array;
  logic [(32)-1:0][XLEN-1:0]        gpr_wdata_array;
  logic [(32)-1:0]                  gpr_wmask_array;
  logic [NMEM-1:0][XLEN-1:0]        mem_addr_array;
  logic [NMEM-1:0][XLEN-1:0]        mem_rdata_array;
  logic [NMEM-1:0][(XLEN/8)-1:0]    mem_rmask_array;
  logic [NMEM-1:0][XLEN-1:0]        mem_wdata_array;
  logic [NMEM-1:0][(XLEN/8)-1:0]    mem_wmask_array;

  logic [5:0]                       cslli_shamt;

  logic                             is_dret;
  logic                             is_mret;
  logic                             is_uret;
  logic                             is_wfi;
  logic                             is_wfe;
  logic                             is_ebreak;
  logic                             is_ebreak_compr;
  logic                             is_ebreak_noncompr;
  logic                             is_ecall;
  logic                             is_cslli;
  logic                             is_nmi;
  logic                             is_compressed;
  logic                             is_dbg_trg;
  logic                             is_mmode;
  logic                             is_not_mmode;
  logic                             is_umode;
  logic                             is_not_umode;
  logic                             is_pma_instr_fault;
  logic                             is_instr_bus_valid;
  logic                             is_pushpop;
  logic                             is_split_datatrans;
  logic                             is_mem_act;
  logic                             is_tablejump_raw;
  logic                             is_pma_fault;
  logic                             is_fencefencei;
  logic [31:0]                      rvfi_mem_addr_word0highbyte;
  logic                             is_load_instr;
  logic                             is_store_instr;
  logic                             is_loadstore_instr;

  logic                             is_nmi_triggered = 0;

  // -------------------------------------------------------------------
  // Begin module code
  // -------------------------------------------------------------------

  // these signals are added to make it easier to use the signal arrays,
  // and to inspect them in the waveforms
  // gpr masks are redundant, but added for ease of use
  assign {>>{gpr_rdata_array}} = rvfi_gpr_rdata;
  assign gpr_rmask_array       = rvfi_gpr_rmask;
  assign {>>{gpr_wdata_array}} = rvfi_gpr_wdata;
  assign gpr_wmask_array       = rvfi_gpr_wmask;


  assign {>>{mem_addr_array}}  = rvfi_mem_addr;
  assign {>>{mem_rdata_array}} = rvfi_mem_rdata;
  assign {>>{mem_rmask_array}} = rvfi_mem_rmask;
  assign {>>{mem_wdata_array}} = rvfi_mem_wdata;
  assign {>>{mem_wmask_array}} = rvfi_mem_wmask;

  assign cslli_shamt = {rvfi_i.rvfi_insn[12], rvfi_i.rvfi_insn[6:2]};

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      nmi_instr_cnt    <= 0;
      is_nmi_triggered <= 0;
    end else begin
      // Detect taken nmi or pending nmi and start counting
      is_nmi_triggered <= is_nmi_triggered ? 1'b1 : (is_nmi || (rvfi_nmip && rvfi_valid));
      if (is_nmi_triggered && rvfi_valid) begin
        nmi_instr_cnt <= nmi_instr_cnt + 1;
      end
    end
    cycle_cnt <= cycle_cnt + 1;
  end

  // assigning signal aliases to helper functions
  always_comb begin
    is_dret             <= is_dret_f();
    is_mret             <= is_mret_f();
    is_uret             <= is_uret_f();
    is_wfi              <= is_wfi_f();
    is_wfe              <= is_wfe_f();
    is_ebreak           <= is_ebreak_f();
    is_ebreak_compr     <= is_ebreak_compr_f();
    is_ebreak_noncompr  <= is_ebreak_noncompr_f();
    is_ecall            <= is_ecall_f();
    is_cslli            <= is_cslli_f();
    is_nmi              <= is_nmi_f();
    is_compressed       <= is_compressed_f();
    is_dbg_trg          <= is_dbg_trg_f();
    is_mmode            <= is_mmode_f();
    is_not_mmode        <= is_not_mmode_f();
    is_umode            <= is_umode_f();
    is_not_umode        <= is_not_umode_f();
    is_pma_instr_fault  <= is_pma_instr_fault_f();
    is_instr_bus_valid  <= is_instr_bus_valid_f();
    is_pushpop          <= is_pushpop_f();
    is_split_datatrans  <= is_split_datatrans_f();
    is_mem_act          <= is_mem_act_f();
    is_tablejump_raw    <= is_tablejump_raw_f();
    is_pma_fault        <= is_pma_fault_f();
    is_fencefencei      <= is_fencefencei_f();
    rvfi_mem_addr_word0highbyte <= rvfi_mem_addr_word0highbyte_f();
  end

  // assigning signals
  always_comb begin
    is_load_instr <= 0; // TODO:ERROR:silabs-robin
    is_store_instr <= 0; // TODO:ERROR:silabs-robin
    is_loadstore_instr <= 0; // TODO:ERROR:silabs-robin
  end

  /**
      * Used by target DUT.
  */
  clocking dut_cb @(posedge clk or reset_n);
  endclocking : dut_cb

  /**
      * Used by uvma_rvfi_instr_mon_c.
  */
  clocking mon_cb @(posedge clk or reset_n);
      input #1step
        cycle_cnt,
        nmi_instr_cnt,
        rvfi_valid,
        rvfi_order,
        rvfi_insn,
        rvfi_trap,
        rvfi_halt,
        rvfi_dbg,
        rvfi_dbg_mode,
        rvfi_nmip,
        rvfi_intr,
        rvfi_mode,
        rvfi_ixl,
        rvfi_pc_rdata,
        rvfi_pc_wdata,
        rvfi_rs1_addr,
        rvfi_rs1_rdata,
        rvfi_rs2_addr,
        rvfi_rs2_rdata,
        rvfi_rs3_addr,
        rvfi_rs3_rdata,
        rvfi_rd1_addr,
        rvfi_rd1_wdata,
        rvfi_rd2_addr,
        rvfi_rd2_wdata,
        rvfi_gpr_rdata,
        rvfi_gpr_rmask,
        rvfi_gpr_wdata,
        rvfi_gpr_wmask,
        rvfi_mem_addr,
        rvfi_mem_rdata,
        rvfi_mem_rmask,
        rvfi_mem_wdata,
        rvfi_mem_wmask;
  endclocking : mon_cb

  modport passive_mp    (clocking mon_cb);

  // -------------------------------------------------------------------
  // Functions
  // -------------------------------------------------------------------

  // NOTE: All of these functions are only valid when the RVFI bus holds
  //       valid values, indicated by rvfi_valid == 1

  // Check if instruction is of a certain type
  // Usage: instr_mask sets the parts of the instruction you want to compare,
  //        instr_ref is the reference to match
  function automatic logic match_instr(
    logic [ DEFAULT_XLEN-1:0] instr_ref,
    logic [ DEFAULT_XLEN-1:0] instr_mask
  );

  return rvfi_valid && is_instr_bus_valid && ((rvfi_insn & instr_mask) == instr_ref);

  endfunction : match_instr

  // Check if instruction is of a certain type, without verifying the instr word is valid
  // Usage: instr_mask sets the parts of the instruction you want to compare,
  //        instr_ref is the reference to match
  function automatic logic match_instr_raw(
    logic [ DEFAULT_XLEN-1:0] instr_ref,
    logic [ DEFAULT_XLEN-1:0] instr_mask
  );

  return rvfi_valid && ((rvfi_insn & instr_mask) == instr_ref);

  endfunction : match_instr_raw

// Match instr types
function automatic logic match_instr_r(logic [ DEFAULT_XLEN-1:0] instr_ref);
  return match_instr(instr_ref, INSTR_MASK_R_TYPE);
endfunction : match_instr_r

function automatic logic match_instr_r_var(
  logic [6:0] funct7,
  logic [2:0] funct3,
  logic [6:0] opcode
);
  return match_instr_r({funct7, 10'b0, funct3, 5'b0, opcode});
endfunction : match_instr_r_var

function automatic logic match_instr_isb(logic [ DEFAULT_XLEN-1:0] instr_ref);
  return match_instr(instr_ref, INSTR_MASK_I_S_B_TYPE);
endfunction : match_instr_isb

function automatic logic match_instr_isb_var (
  logic [2:0] funct3,
  logic [6:0] opcode
);
  return match_instr_isb({17'b0, funct3, 5'b0, opcode});
endfunction : match_instr_isb_var

function automatic logic match_instr_uj(logic [ DEFAULT_XLEN-1:0] instr_ref);
  return  match_instr(instr_ref, INSTR_MASK_U_J_TYPE);
endfunction : match_instr_uj

function automatic logic match_instr_uj_var(logic [6:0] opcode);
  return  match_instr_uj({25'b0, opcode});
endfunction : match_instr_uj_var

// Match CSR functions
// These instruction are used to check for csr activity.
// All instructions has the input csr_addr. Setting this limits the query to
// that single address, leaving the input as 0 returns any csr activity.
function automatic logic is_csr_instr(logic [11:0] csr_addr = 0);
  if (csr_addr == 0) begin //not specified
    return  match_instr_isb(INSTR_OPCODE_CSRRW)  ||
            match_instr_isb(INSTR_OPCODE_CSRRS)  ||
            match_instr_isb(INSTR_OPCODE_CSRRC)  ||
            match_instr_isb(INSTR_OPCODE_CSRRWI) ||
            match_instr_isb(INSTR_OPCODE_CSRRSI) ||
            match_instr_isb(INSTR_OPCODE_CSRRCI);
  end else begin
    return  match_instr(32'h0 | (csr_addr << INSTR_CSRADDR_POS), INSTR_MASK_CSRADDR) &&
            ( match_instr_isb(INSTR_OPCODE_CSRRW)  ||
              match_instr_isb(INSTR_OPCODE_CSRRS)  ||
              match_instr_isb(INSTR_OPCODE_CSRRC)  ||
              match_instr_isb(INSTR_OPCODE_CSRRWI) ||
              match_instr_isb(INSTR_OPCODE_CSRRSI) ||
              match_instr_isb(INSTR_OPCODE_CSRRCI));
  end
endfunction : is_csr_instr

// This function follows the spec definition of a csr read
function automatic logic is_csr_read(logic [11:0] csr_addr = 0);
  if (  (rvfi_rd1_addr == 0) &&
        (   match_instr_isb(INSTR_OPCODE_CSRRW) ||
            match_instr_isb(INSTR_OPCODE_CSRRWI))) begin
    return 0;
  end else begin
    return is_csr_instr(csr_addr);
  end
endfunction

// This function follows the spec definition of a csr write
function automatic logic is_csr_write(logic [11:0] csr_addr = 0);
  if (  ( (rvfi_rs1_addr == 0) &&
          (   match_instr_isb(INSTR_OPCODE_CSRRS) ||
              match_instr_isb(INSTR_OPCODE_CSRRC))
        ) || (
          ((rvfi_insn & INSTR_MASK_CSRUIMM) == 0) &&
          (   match_instr_isb(INSTR_OPCODE_CSRRSI) ||
              match_instr_isb(INSTR_OPCODE_CSRRCI))
        )) begin
    return 0;
  end else begin
    return is_csr_instr(csr_addr);
  end
endfunction

// returns intended write data for any CSR write instruction,
// without regard for what the legal values are in the CSR
// input current value of the csr, and the csr address
// NOTE: that this will work for CSRRW with unspecified csr address,
// but CSRRS/CSRRC will give incorrect return values
function automatic logic [DEFAULT_XLEN-1:0] csr_intended_wdata( logic [DEFAULT_XLEN-1:0] csr_rdata,
                                                                logic [11:0] csr_addr = 0);
  if (!is_csr_write(csr_addr)) begin
    return 0;
  end else begin
    if (match_instr_isb(INSTR_OPCODE_CSRRW)) begin
      return rvfi_rs1_rdata;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRWI)) begin
      return (rvfi_insn & INSTR_MASK_CSRUIMM) >> INSTR_CSRUIMM_POS;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRS)) begin
      return csr_rdata | rvfi_rs1_rdata;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRSI)) begin
      return csr_rdata | ((rvfi_insn & INSTR_MASK_CSRUIMM) >> INSTR_CSRUIMM_POS);
     end else if (match_instr_isb(INSTR_OPCODE_CSRRC)) begin
      return csr_rdata & ~rvfi_rs1_rdata;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRCI)) begin
      return csr_rdata & ~((rvfi_insn & INSTR_MASK_CSRUIMM) >> INSTR_CSRUIMM_POS);
    end
  end
endfunction

// Return wdata of register "gpr"
function automatic logic [ DEFAULT_XLEN-1:0] get_gpr_wdata( int gpr);
  return rvfi_gpr_wdata[gpr* DEFAULT_XLEN +: DEFAULT_XLEN];
endfunction : get_gpr_wdata

// Return rdata of register "gpr"
function automatic logic [ DEFAULT_XLEN-1:0] get_gpr_rdata( int gpr);
  return rvfi_gpr_rdata[gpr* DEFAULT_XLEN +: DEFAULT_XLEN];
endfunction : get_gpr_rdata

// Return valid data of memory transaction "txn"
function automatic logic [ DEFAULT_XLEN-1:0] get_mem_data_word( int txn);
  bit [ DEFAULT_XLEN-1:0] ret;

  for (int i = 0; i <  DEFAULT_XLEN/8; i++) begin
    if (rvfi_mem_wmask[(txn* DEFAULT_XLEN/8) + i]) begin
      ret[i*8 +:8] = rvfi_mem_wdata[((txn* DEFAULT_XLEN) + (i*8)) +:8];
    end else begin
      ret[i*8 +:8] = rvfi_mem_rdata[((txn* DEFAULT_XLEN) + (i*8)) +:8];
    end
  end

  return ret;

endfunction : get_mem_data_word

//Return addr of memory transaction "txn"
function automatic logic [ DEFAULT_XLEN-1:0] get_mem_addr(int txn);

  return rvfi_mem_addr[txn* DEFAULT_XLEN +: DEFAULT_XLEN];

endfunction : get_mem_addr

//Return rmask of memory transaction "txn"
function automatic logic [( DEFAULT_XLEN/8)-1:0] get_mem_rmask(int txn);

  return rvfi_mem_rmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)];

endfunction : get_mem_rmask

//Return wmask of memory transaction "txn"
function automatic logic [( DEFAULT_XLEN/8)-1:0] get_mem_wmask(int txn);

  return rvfi_mem_wmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)];

endfunction : get_mem_wmask


//Check memory transaction activity

//Checks if a position in the rvfi memory transaction list
//indicates any activity.
//return {read, write}
function automatic logic [1:0] check_mem_act(int txn);
  bit read = 0;
  bit write = 0;

  if (rvfi_mem_rmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)]) begin
    read = 1;
  end
  if (rvfi_mem_wmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)]) begin
    write = 1;
  end

  return {read,write};

endfunction : check_mem_act

function automatic logic is_mem_act_f();
  return  rvfi_valid && (|rvfi_mem_rmask || |rvfi_mem_wmask);
endfunction : is_mem_act_f


// Short functions for recognising special functions

function automatic logic is_dret_f();
  return match_instr(INSTR_OPCODE_DRET, INSTR_MASK_FULL);
endfunction : is_dret_f

function automatic logic is_mret_f();
  return match_instr(INSTR_OPCODE_MRET, INSTR_MASK_FULL);
endfunction : is_mret_f

function automatic logic is_uret_f();
  return match_instr(INSTR_OPCODE_URET, INSTR_MASK_FULL);
endfunction : is_uret_f

function automatic logic is_wfi_f();
  return match_instr(INSTR_OPCODE_WFI, INSTR_MASK_FULL);
endfunction : is_wfi_f

function automatic logic is_wfe_f();
  return match_instr(INSTR_OPCODE_WFE, INSTR_MASK_FULL);
endfunction : is_wfe_f

function automatic logic is_ebreak_f();
  return match_instr(INSTR_OPCODE_EBREAK, INSTR_MASK_FULL) || match_instr(INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
endfunction : is_ebreak_f

function automatic logic is_ebreak_compr_f();
  return match_instr(INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
endfunction : is_ebreak_compr_f

function automatic logic is_ebreak_noncompr_f();
  return match_instr(INSTR_OPCODE_EBREAK, INSTR_MASK_FULL);
endfunction : is_ebreak_noncompr_f

function automatic logic is_ecall_f();
  return match_instr(INSTR_OPCODE_ECALL, INSTR_MASK_FULL);
endfunction : is_ecall_f

function logic is_cslli_f();
  return match_instr(INSTR_OPCODE_CSLLI, INSTR_MASK_CMPR);
endfunction : is_cslli_f

function automatic logic is_pushpop_f();
  return  match_instr(INSTR_OPCODE_PUSH,    INSTR_MASK_PUSHPOP)  ||
          match_instr(INSTR_OPCODE_POP,     INSTR_MASK_PUSHPOP)  ||
          match_instr(INSTR_OPCODE_POPRET,  INSTR_MASK_PUSHPOP)  ||
          match_instr(INSTR_OPCODE_POPRETZ, INSTR_MASK_PUSHPOP);
endfunction : is_pushpop_f

function automatic logic is_tablejump_raw_f();
  return  match_instr_raw(INSTR_OPCODE_TABLEJUMP, INSTR_MASK_TABLEJUMP);
endfunction : is_tablejump_raw_f

function automatic logic is_fencefencei_f();
  return  match_instr(INSTR_OPCODE_FENCE,  INSTR_MASK_FENCE)  ||
          match_instr(INSTR_OPCODE_FENCEI, INSTR_MASK_FENCEI);
endfunction : is_fencefencei_f

function automatic logic is_nmi_f();
  return rvfi_valid && rvfi_intr.intr && (rvfi_intr.cause & INTR_CAUSE_NMI_MASK);
endfunction : is_nmi_f

function automatic logic is_compressed_f();
  return  rvfi_valid && (rvfi_insn[1:0] != 2'b11);
endfunction : is_compressed_f

function automatic logic is_dbg_trg_f();
  return  rvfi_valid &&
          rvfi_trap.trap &&
          rvfi_trap.debug &&
         (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER);
endfunction : is_dbg_trg_f

function automatic logic is_mmode_f();
  return  rvfi_valid &&
          (rvfi_mode == PRIV_LVL_M);
endfunction : is_mmode_f

function automatic logic is_not_mmode_f();
  return  rvfi_valid &&
          (rvfi_mode != PRIV_LVL_M);
endfunction : is_not_mmode_f

function automatic logic is_umode_f();
  return  rvfi_valid &&
          (rvfi_mode == PRIV_LVL_U);
endfunction : is_umode_f

function automatic logic is_not_umode_f();
  return  rvfi_valid &&
          (rvfi_mode != PRIV_LVL_U);
endfunction : is_not_umode_f

function automatic logic is_pma_instr_fault_f();
  return  rvfi_valid  &&
          rvfi_trap.trap  &&
          rvfi_trap.exception  &&
          (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_FAULT)  &&
          (rvfi_trap.cause_type == 'h 0);
endfunction : is_pma_instr_fault_f

function automatic logic is_pma_fault_f();
  return  rvfi_valid  &&
          rvfi_trap.trap  &&
          rvfi_trap.exception  &&
          (rvfi_trap.exception_cause  inside {
            EXC_CAUSE_INSTR_FAULT,
            EXC_CAUSE_LOAD_FAULT,
            EXC_CAUSE_STORE_FAULT
          })  &&
          (rvfi_trap.cause_type == 'h 0);
endfunction : is_pma_fault_f

function automatic logic is_instr_bus_valid_f();
  return !( (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_FAULT) ||
            (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_INTEGRITY_FAULT) ||
            (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_BUS_FAULT)
    );
endfunction : is_instr_bus_valid_f

function automatic logic [31:0] rvfi_mem_addr_word0highbyte_f();
  logic [31:0] addr = rvfi_mem_addr[31:0];
  case (1)
    (rvfi_mem_rmask[3] || rvfi_mem_wmask[3]):
      return  addr + 3;
    (rvfi_mem_rmask[2] || rvfi_mem_wmask[2]):
      return  addr + 2;
    (rvfi_mem_rmask[1] || rvfi_mem_wmask[1]):
      return  addr + 1;
    default:
      return  addr;
  endcase
endfunction : rvfi_mem_addr_word0highbyte_f

function automatic logic is_split_datatrans_f();
  logic [31:0]  low_addr  = rvfi_mem_addr;
  logic [31:0]  high_addr = rvfi_mem_addr_word0highbyte;
  return  is_mem_act && (low_addr[31:2] != high_addr[31:2]);
endfunction : is_split_datatrans_f


endinterface : uvma_rvfi_instr_if_t


`endif // __UVMA_RVFI_INSTR_IF_SV__
