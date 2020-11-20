// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Instruction Decode Stage                                   //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_id_stage_sva import cv32e40p_pkg::*; import cv32e40p_apu_core_pkg::*;
#(
  parameter PULP_XPULP        =  1,                     // PULP ISA Extension (including PULP specific CSRs and hardware loop, excluding p.elw)
  parameter PULP_CLUSTER      =  0,
  parameter N_HWLP            =  2,
  parameter N_HWLP_BITS       =  $clog2(N_HWLP),
  parameter PULP_SECURE       =  0,
  parameter USE_PMP           =  0,
  parameter A_EXTENSION       =  0,
  parameter APU               =  0,
  parameter FPU               =  0,
  parameter PULP_ZFINX        =  0,
  parameter APU_NARGS_CPU     =  3,
  parameter APU_WOP_CPU       =  6,
  parameter APU_NDSFLAGS_CPU  = 15,
  parameter APU_NUSFLAGS_CPU  =  5,
  parameter DEBUG_TRIGGER_EN  =  1
)
(
    input  logic        clk,                    // Gated clock
    input  logic        clk_ungated_i,          // Ungated clock
    input  logic        rst_n,

    input  logic        scan_cg_en_i,

    input  logic        fetch_enable_i,
    input  logic        ctrl_busy_o,
    input  logic        is_decoding_o,

    // Interface to IF stage
    input  logic              instr_valid_i,
    input  logic       [31:0] instr_rdata_i,      // comes from pipeline of IF stage
    input  logic              instr_req_o,
    input  logic              is_compressed_i,
    input  logic              illegal_c_insn_i,

    // Jumps and branches
    input  logic        branch_in_ex_o,
    input  logic        branch_decision_i,
    input  logic [31:0] jump_target_o,

    // IF and ID stage signals
    input  logic        clear_instr_valid_o,
    input  logic        pc_set_o,
    input  logic [3:0]  pc_mux_o,
    input  logic [2:0]  exc_pc_mux_o,
    input  logic [1:0]  trap_addr_mux_o,


    input  logic        is_fetch_failed_i,

    input  logic [31:0] pc_id_i,

    // Stalls
    input  logic        halt_if_o,      // controller requests a halt of the IF stage

    input  logic        id_ready_o,     // ID stage is ready for the next instruction
    input  logic        ex_ready_i,     // EX stage is ready for the next instruction
    input  logic        wb_ready_i,     // WB stage is ready for the next instruction

    input  logic        id_valid_o,     // ID stage is done
    input  logic        ex_valid_i,     // EX stage is done

    // Pipeline ID/EX
    input  logic [31:0] pc_ex_o,

    input  logic [31:0] alu_operand_a_ex_o,
    input  logic [31:0] alu_operand_b_ex_o,
    input  logic [31:0] alu_operand_c_ex_o,
    input  logic [ 4:0] bmask_a_ex_o,
    input  logic [ 4:0] bmask_b_ex_o,
    input  logic [ 1:0] imm_vec_ext_ex_o,
    input  logic [ 1:0] alu_vec_mode_ex_o,

    input  logic [5:0]  regfile_waddr_ex_o,
    input  logic        regfile_we_ex_o,

    input  logic [5:0]  regfile_alu_waddr_ex_o,
    input  logic        regfile_alu_we_ex_o,

    // ALU
    input  logic        alu_en_ex_o,
    input  logic [ALU_OP_WIDTH-1:0] alu_operator_ex_o,
    input  logic        alu_is_clpx_ex_o,
    input  logic        alu_is_subrot_ex_o,
    input  logic [ 1:0] alu_clpx_shift_ex_o,

    // MUL
    input  logic [ 2:0] mult_operator_ex_o,
    input  logic [31:0] mult_operand_a_ex_o,
    input  logic [31:0] mult_operand_b_ex_o,
    input  logic [31:0] mult_operand_c_ex_o,
    input  logic        mult_en_ex_o,
    input  logic        mult_sel_subword_ex_o,
    input  logic [ 1:0] mult_signed_mode_ex_o,
    input  logic [ 4:0] mult_imm_ex_o,

    input  logic [31:0] mult_dot_op_a_ex_o,
    input  logic [31:0] mult_dot_op_b_ex_o,
    input  logic [31:0] mult_dot_op_c_ex_o,
    input  logic [ 1:0] mult_dot_signed_ex_o,
    input  logic        mult_is_clpx_ex_o,
    input  logic [ 1:0] mult_clpx_shift_ex_o,
    input  logic        mult_clpx_img_ex_o,

    // APU
    input  logic                        apu_en_ex_o,
    input  logic [APU_WOP_CPU-1:0]      apu_op_ex_o,
    input  logic [1:0]                  apu_lat_ex_o,
    input  logic [APU_NARGS_CPU-1:0][31:0]                 apu_operands_ex_o,
    input  logic [APU_NDSFLAGS_CPU-1:0] apu_flags_ex_o,
    input  logic [5:0]                  apu_waddr_ex_o,

    input  logic [2:0][5:0]            apu_read_regs_o,
    input  logic [2:0]                 apu_read_regs_valid_o,
    input  logic                       apu_read_dep_i,
    input  logic [1:0][5:0]            apu_write_regs_o,
    input  logic [1:0]                 apu_write_regs_valid_o,
    input  logic                       apu_write_dep_i,
    input  logic                       apu_perf_dep_o,
    input  logic                       apu_busy_i,
    input  logic [C_RM-1:0]            frm_i,

    // CSR ID/EX
    input  logic        csr_access_ex_o,
    input  logic [1:0]  csr_op_ex_o,
    input  PrivLvl_t    current_priv_lvl_i,
    input  logic        csr_irq_sec_o,
    input  logic [5:0]  csr_cause_o,
    input  logic        csr_save_if_o,
    input  logic        csr_save_id_o,
    input  logic        csr_save_ex_o,
    input  logic        csr_restore_mret_id_o,
    input  logic        csr_restore_uret_id_o,
    input  logic        csr_restore_dret_id_o,
    input  logic        csr_save_cause_o,

    // hwloop signals
    input  logic [N_HWLP-1:0] [31:0] hwlp_start_o,
    input  logic [N_HWLP-1:0] [31:0] hwlp_end_o,
    input  logic [N_HWLP-1:0] [31:0] hwlp_cnt_o,
    input  logic                     hwlp_jump_o,
    input  logic [31:0]              hwlp_target_o,

    // hwloop signals from CS register
    input  logic   [N_HWLP_BITS-1:0] csr_hwlp_regid_i,
    input  logic               [2:0] csr_hwlp_we_i,
    input  logic              [31:0] csr_hwlp_data_i,

    // Interface to load store unit
    input  logic        data_req_ex_o,
    input  logic        data_we_ex_o,
    input  logic [1:0]  data_type_ex_o,
    input  logic [1:0]  data_sign_ext_ex_o,
    input  logic [1:0]  data_reg_offset_ex_o,
    input  logic        data_load_event_ex_o,

    input  logic        data_misaligned_ex_o,

    input  logic        prepost_useincr_ex_o,
    input  logic        data_misaligned_i,
    input  logic        data_err_i,
    input  logic        data_err_ack_o,

    input  logic [5:0]  atop_ex_o,

    // Interrupt signals
    input  logic [31:0] irq_i,
    input  logic        irq_sec_i,
    input  logic [31:0] mie_bypass_i,           // MIE CSR (bypass)
    input  logic [31:0] mip_o,                  // MIP CSR
    input  logic        m_irq_enable_i,
    input  logic        u_irq_enable_i,
    input  logic        irq_ack_o,
    input  logic [4:0]  irq_id_o,
    input  logic [4:0]  exc_cause_o,

    // Debug Signal
    input  logic        debug_mode_o,
    input  logic [2:0]  debug_cause_o,
    input  logic        debug_csr_save_o,
    input  logic        debug_req_i,
    input  logic        debug_single_step_i,
    input  logic        debug_ebreakm_i,
    input  logic        debug_ebreaku_i,
    input  logic        trigger_match_i,
    input  logic        debug_p_elw_no_sleep_o,
    input  logic        debug_havereset_o,
    input  logic        debug_running_o,
    input  logic        debug_halted_o,

    // Wakeup Signal
    input  logic        wake_from_sleep_o,

    // Forward Signals
    input  logic [5:0]  regfile_waddr_wb_i,
    input  logic        regfile_we_wb_i,
    input  logic [31:0] regfile_wdata_wb_i, // From wb_stage: selects data from data memory, ex_stage result and sp rdata

    input  logic [5:0]  regfile_alu_waddr_fw_i,
    input  logic        regfile_alu_we_fw_i,
    input  logic [31:0] regfile_alu_wdata_fw_i,

    // from ALU
    input  logic        mult_multicycle_i,    // when we need multiple cycles in the multiplier and use op c as storage

    // Performance Counters
    input  logic        mhpmevent_minstret_o,
    input  logic        mhpmevent_load_o,
    input  logic        mhpmevent_store_o,
    input  logic        mhpmevent_jump_o,
    input  logic        mhpmevent_branch_o,
    input  logic        mhpmevent_branch_taken_o,
    input  logic        mhpmevent_compressed_o,
    input  logic        mhpmevent_jr_stall_o,
    input  logic        mhpmevent_imiss_o,
    input  logic        mhpmevent_ld_stall_o,
    input  logic        mhpmevent_pipe_stall_o,

    input  logic        perf_imiss_i,
    input  logic [31:0] mcounteren_i,

	// internal nets from cv32e40p_prefetch_controller that the Assertions need to "see".
	input  logic [31:0] instr,
	input  logic        alu_en,
	input  logic        mult_en,
	input  logic        mult_int_en,
	input  logic        mult_dot_en,
    input  logic        ebrk_insn_dec,
    input  logic        mret_insn_dec,
    input  logic        uret_insn_dec,
    input  logic        dret_insn_dec,
    input  logic        ecall_insn_dec,
    input  logic        wfi_insn_dec,
    input  logic        fencei_insn_dec,
	input  logic        regfile_we_id,
	input  logic        regfile_alu_we_id,
	input  logic        data_req_id,
    input  logic        branch_taken_ex,
    input  logic        apu_en,
    input  logic        illegal_insn_dec,
    input  logic [ALU_OP_WIDTH-1:0] alu_operator,
    input  logic [ 1:0] alu_vec_mode,
    input  logic [ 2:0] mult_operator,
    input  logic [ 1:0] csr_op
);

    import uvm_pkg::*; // needed for the UVM messaging service (`uvm_error(), etc.)

    always_comb begin
      if (FPU==1) begin
        assert (APU_NDSFLAGS_CPU >= C_RM+2*cv32e40p_fpu_pkg::FP_FORMAT_BITS+cv32e40p_fpu_pkg::INT_FORMAT_BITS)
          else `uvm_error("ID STAGE ASSERTION", $sformatf("APU_NDSFLAGS_CPU APU flagbits is smaller than %0d",
			                                              C_RM+2*cv32e40p_fpu_pkg::FP_FORMAT_BITS+cv32e40p_fpu_pkg::INT_FORMAT_BITS))
      end
    end

    // make sure that branch decision is valid when jumping
    a_br_decision : assert property (
      @(posedge clk) (branch_in_ex_o) |-> (branch_decision_i !== 1'bx) )
	  else `uvm_error("ID STAGE ASSERTION", "Branch decision is X")

    // the instruction delivered to the ID stage should always be valid
    a_valid_instr : assert property (
      @(posedge clk) (instr_valid_i & (~illegal_c_insn_i)) |-> (!$isunknown(instr)) )
	  else `uvm_error("ID STAGE ASSERTION", "Instruction is valid, but has at least one X")

    // Check that instruction after taken branch is flushed (more should actually be flushed, but that is not checked here)
    // and that EX stage is ready to receive flushed instruction immediately
    property p_branch_taken_ex;
       @(posedge clk) disable iff (!rst_n) (branch_taken_ex == 1'b1) |-> ((ex_ready_i == 1'b1) &&
                                                                          (alu_en == 1'b0) && (apu_en == 1'b0) &&
                                                                          (mult_en == 1'b0) && (mult_int_en == 1'b0) &&
                                                                          (mult_dot_en == 1'b0) && (regfile_we_id == 1'b0) &&
                                                                          (regfile_alu_we_id == 1'b0) && (data_req_id == 1'b0));
    endproperty

    a_branch_taken_ex : assert property(p_branch_taken_ex) else `uvm_error("ID STAGE ASSERTION", "Instruction after taken branch not flushed")

    // Check that if IRQ PC update does not coincide with IRQ related CSR write
    // MIE is excluded from the check because it has a bypass.
    property p_irq_csr;
       @(posedge clk) disable iff (!rst_n) (pc_set_o && (pc_mux_o == PC_EXCEPTION) && ((exc_pc_mux_o == EXC_PC_EXCEPTION) || (exc_pc_mux_o == EXC_PC_IRQ)) &&
                                            csr_access_ex_o && (csr_op_ex_o != CSR_OP_READ)) |->
                                           ((alu_operand_b_ex_o[11:0] != CSR_MSTATUS) && (alu_operand_b_ex_o[11:0] != CSR_USTATUS) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MEPC) && (alu_operand_b_ex_o[11:0] != CSR_UEPC) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MCAUSE) && (alu_operand_b_ex_o[11:0] != CSR_UCAUSE) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MTVEC) && (alu_operand_b_ex_o[11:0] != CSR_UTVEC));
    endproperty

    a_irq_csr : assert property(p_irq_csr) else `uvm_error("ID STAGE ASSERTION", "CSR write to MIE is not excluded on IRQ PC update not coinciding with IRQ")

    // Check that xret does not coincide with CSR write (to avoid using wrong return address)
    // This check is more strict than really needed; a CSR instruction would be allowed in EX as long
    // as its write action happens before the xret CSR usage
    property p_xret_csr;
       @(posedge clk) disable iff (!rst_n) (pc_set_o && ((pc_mux_o == PC_MRET) || (pc_mux_o == PC_URET) || (pc_mux_o == PC_DRET))) |->
                                           (!(csr_access_ex_o && (csr_op_ex_o != CSR_OP_READ)));
    endproperty

    a_xret_csr : assert property(p_xret_csr) else `uvm_error("ID STAGE ASSERTION", $sformatf("Check that xret does not coincide with CSR write, pc_mux_o = %h", pc_mux_o))

    generate
    if (!A_EXTENSION) begin : gen_no_a_extension_assertions

      // Check that A extension opcodes are decoded as illegal when A extension not enabled
      property p_illegal_0;
         @(posedge clk) disable iff (!rst_n) (instr[6:0] == OPCODE_AMO) |-> (illegal_insn_dec == 'b1);
      endproperty

      a_illegal_0 : assert property(p_illegal_0) else `uvm_error("ID STAGE ASSERTION", "A_EXTENSION is not set, so A instructions should be illegal!")

    end
    endgenerate

    generate
    if (!PULP_XPULP) begin : gen_no_pulp_xpulp_assertions

      // Check that PULP extension opcodes are decoded as illegal when PULP extension is not enabled
      property p_illegal_1;
         @(posedge clk) disable iff (!rst_n) ((instr[6:0] == OPCODE_LOAD_POST) || (instr[6:0] == OPCODE_STORE_POST) || (instr[6:0] == OPCODE_PULP_OP) ||
                                              (instr[6:0] == OPCODE_HWLOOP) || (instr[6:0] == OPCODE_VECOP)) |-> (illegal_insn_dec == 'b1);
      endproperty

      a_illegal_1 : assert property(p_illegal_1) else `uvm_error("ID STAGE ASSERTION", "PULP extension not set, so PULP instructions should be illegal!")

      // Check that certain ALU operations are not used when PULP extension is not enabled
      property p_alu_op;
         @(posedge clk) disable iff (!rst_n) (1'b1) |-> ( (alu_operator != ALU_ADDU ) && (alu_operator != ALU_SUBU ) &&
                                                           (alu_operator != ALU_ADDR ) && (alu_operator != ALU_SUBR ) &&
                                                           (alu_operator != ALU_ADDUR) && (alu_operator != ALU_SUBUR) &&
                                                           (alu_operator != ALU_ROR) && (alu_operator != ALU_BEXT) &&
                                                           (alu_operator != ALU_BEXTU) && (alu_operator != ALU_BINS) &&
                                                           (alu_operator != ALU_BCLR) && (alu_operator != ALU_BSET) &&
                                                           (alu_operator != ALU_BREV) && (alu_operator != ALU_FF1) &&
                                                           (alu_operator != ALU_FL1) && (alu_operator != ALU_CNT) &&
                                                           (alu_operator != ALU_CLB) && (alu_operator != ALU_EXTS) &&
                                                           (alu_operator != ALU_EXT) && (alu_operator != ALU_LES) &&
                                                           (alu_operator != ALU_LEU) && (alu_operator != ALU_GTS) &&
                                                           (alu_operator != ALU_GTU) && (alu_operator != ALU_SLETS) &&
                                                           (alu_operator != ALU_SLETU) && (alu_operator != ALU_ABS) &&
                                                           (alu_operator != ALU_CLIP) && (alu_operator != ALU_CLIPU) &&
                                                           (alu_operator != ALU_INS) && (alu_operator != ALU_MIN) &&
                                                           (alu_operator != ALU_MINU) && (alu_operator != ALU_MAX) &&
                                                           (alu_operator != ALU_MAXU) && (alu_operator != ALU_SHUF) &&
                                                           (alu_operator != ALU_SHUF2) && (alu_operator != ALU_PCKLO) &&
                                                           (alu_operator != ALU_PCKHI) );
      endproperty

      a_alu_op : assert property(p_alu_op) else `uvm_error("ID STAGE ASSERTION", "Unexpected ALU operator when PULP extension not enabled")

      // Check that certain vector modes are not used when PULP extension is not enabled
      property p_vector_mode;
         @(posedge clk) disable iff (!rst_n) (1'b1) |-> ( (alu_vec_mode != VEC_MODE8 ) && (alu_vec_mode != VEC_MODE16 ) );
      endproperty

      a_vector_mode : assert property(p_vector_mode) else `uvm_error("ID STAGE ASSERTION", "Unexpected vector mode when PULP extension not enabled")

      // Check that certain multiplier operations are not used when PULP extension is not enabled
      property p_mul_op;
         @(posedge clk) disable iff (!rst_n) (mult_int_en == 1'b1) |-> ( (mult_operator != MUL_MSU32) && (mult_operator != MUL_I) &&
                                                                         (mult_operator != MUL_IR) && (mult_operator != MUL_DOT8) &&
                                                                         (mult_operator != MUL_DOT16) );
      endproperty

      a_mul_op : assert property(p_mul_op) else `uvm_error("ID STAGE ASSERTION", "PULP mult operation when no PULP extension enabled")

    end
    endgenerate

    // Check that illegal instruction has no other side effects
    property p_illegal_2;
       @(posedge clk) disable iff (!rst_n) (illegal_insn_dec == 1'b1) |-> !(ebrk_insn_dec || mret_insn_dec || uret_insn_dec || dret_insn_dec ||
                                                                            ecall_insn_dec || wfi_insn_dec || fencei_insn_dec ||
                                                                            alu_en || mult_int_en || mult_dot_en || apu_en ||
                                                                            regfile_we_id || regfile_alu_we_id ||
                                                                            csr_op != CSR_OP_READ || data_req_id);
    endproperty

    a_illegal_2 : assert property(p_illegal_2) else `uvm_error("ID STAGE ASSERTION", "Illegal instruction side effect detected")

	// COVERAGE ASSERTIONS

    // ensure that jump stalls are exercised
    property p_jr_stall;
       @(posedge clk) disable iff (!rst_n) (mhpmevent_jr_stall_o == 1'b1);
    endproperty

    c_jr_stall : cover property(p_jr_stall);

    // ensure that load stalls are exercised
    property p_ld_stall;
       @(posedge clk) disable iff (!rst_n) (mhpmevent_ld_stall_o == 1'b1);
    endproperty

    c_ld_stall : cover property(p_ld_stall);

		
endmodule // cv32e40p_id_stage_sva
