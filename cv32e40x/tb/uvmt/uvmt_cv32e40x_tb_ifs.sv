
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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
//



// This file specifies all interfaces used by the CV32E40X test bench (uvmt_cv32e40x_tb).
// Most interfaces support tasks to allow control by the ENV or test cases.

`ifndef __UVMT_CV32E40X_TB_IFS_SV__
`define __UVMT_CV32E40X_TB_IFS_SV__


/**
 * clocks and reset
 */
interface uvmt_cv32e40x_clk_gen_if (output logic core_clock, output logic core_reset_n);

   import uvm_pkg::*;

   bit       start_clk               = 0;
   // TODO: get the uvme_cv32e40x_* values from random ENV CFG members.
   realtime  core_clock_period       = 1500ps; // uvme_cv32e40x_clk_period * 1ps;
   realtime  reset_deassert_duration = 7400ps; // uvme_cv32e40x_reset_deassert_duarion * 1ps;
   realtime  reset_assert_duration   = 7400ps; // uvme_cv32e40x_reset_assert_duarion * 1ps;

   /**
    * Generates clock and reset signals.
    * If reset_n comes up de-asserted (1'b1), wait a bit, then assert, then de-assert
    * Otherwise, leave reset asserted, wait a bit, then de-assert.
    */
   initial begin
      core_clock   = 0; // uvme_cv32e40x_clk_initial_value;
      core_reset_n = 0; // uvme_cv32e40x_reset_initial_value;
      wait (start_clk);
      fork
         forever begin
            #(core_clock_period/2) core_clock = ~core_clock;
         end
         begin
           if (core_reset_n == 1'b1) #(reset_deassert_duration);
           core_reset_n = 1'b0;
           #(reset_assert_duration);
           core_reset_n = 1'b1;
         end
      join_none
   end

   /**
    * Sets clock period in ps.
    */
   function void set_clk_period ( real clk_period );
      core_clock_period = clk_period * 1ps;
   endfunction : set_clk_period

   /** Triggers the generation of clk. */
   function void start();
      start_clk = 1;
      `uvm_info("CLK_GEN_IF", "uvmt_cv32e40x_clk_gen_if.start() called", UVM_NONE)
   endfunction : start

endinterface : uvmt_cv32e40x_clk_gen_if

/**
 * Status information generated by the Virtual Peripherals in the DUT WRAPPER memory.
 */
interface uvmt_cv32e40x_vp_status_if (
                                  output bit        tests_passed,
                                  output bit        tests_failed,
                                  output bit        exit_valid,
                                  output bit [31:0] exit_value
                                 );

  import uvm_pkg::*;

  // TODO: X/Z checks
  initial begin
  end

endinterface : uvmt_cv32e40x_vp_status_if



/**
 * Core status signals.
 */
interface uvmt_cv32e40x_core_status_if (
                                    input  wire        core_busy,
                                    input  logic       sec_lvl
                                   );

  import uvm_pkg::*;

endinterface : uvmt_cv32e40x_core_status_if

// Interface to debug assertions and covergroups
interface uvmt_cv32e40x_debug_cov_assert_if
    import cv32e40x_pkg::*;
    (
    input  clk_i,
    input  rst_ni,

    // External interrupt interface
    input  [31:0] irq_i,
    input         irq_ack_o,
    input  [4:0]  irq_id_o,
    input  [31:0] mie_q,

    input         ex_stage_csr_en,
    input         ex_valid,
    input  [31:0] ex_stage_instr_rdata_i,
    input  [31:0] ex_stage_pc,
    input         wb_stage_instr_valid_i,
    input  [31:0] wb_stage_instr_rdata_i,
    input  [31:0] wb_stage_pc, // Program counter in writeback
    input         wb_illegal,
    input         wb_valid,
    input         wb_err,
    input         id_valid,
    input wire ctrl_state_e  ctrl_fsm_cs,            // Controller FSM states with debug_req
    input         illegal_insn_i,
    input         ecall_insn_i,

    input  [31:0] boot_addr_i,

    input         rvfi_valid,
    input  [31:0] rvfi_pc_wdata,
    input  [31:0] rvfi_pc_rdata,

    // Debug signals
    input         debug_req_i, // From controller
    input         debug_req_q, // From controller
    input         pending_debug, // From controller
    input         debug_mode_q, // From controller
    input  [31:0] dcsr_q, // From controller
    input  [31:0] depc_q, // From cs regs  //TODO:ropeders rename "dpc_q"
    input  [31:0] depc_n,
    input  [31:0] dm_halt_addr_i,
    input  [31:0] dm_exception_addr_i,

    input  [5:0]  mcause_q,
    input  [31:0] mtvec,
    input  [31:0] mepc_q,
    input  [31:0] tdata1,
    input  [31:0] tdata2,
    input  trigger_match_i,

    // Counter related input from cs_registers
    input  [31:0] mcountinhibit_q,
    input  [63:0] mcycle,
    input  [63:0] minstret,
    input  inst_ret,

    // WFI Interface
    input  core_sleep_o,

    input  fence_i,

    input  csr_access,
    input  [1:0] csr_op,
    input  [11:0] csr_addr,
    input  csr_we_int,

    output logic is_wfi,
    output logic in_wfi,
    output logic dpc_will_hit,
    output logic addr_match,
    output logic is_ebreak,
    output logic is_cebreak,
    output logic is_dret,
    output logic is_mulhsu,
    output logic [31:0] pending_enabled_irq,
    input  pc_set,
    input  branch_in_ex
);

  clocking mon_cb @(posedge clk_i);
    input #1step

    irq_i,
    irq_ack_o,
    irq_id_o,
    mie_q,

    wb_stage_instr_valid_i,
    wb_stage_instr_rdata_i,
    wb_valid,

    ctrl_fsm_cs,
    illegal_insn_i,
    ecall_insn_i,
    boot_addr_i,
    rvfi_pc_wdata,
    rvfi_pc_rdata,
    debug_req_i,
    debug_mode_q,
    dcsr_q,
    depc_q,
    depc_n,
    dm_halt_addr_i,
    dm_exception_addr_i,
    mcause_q,
    mtvec,
    mepc_q,
    tdata1,
    tdata2,
    trigger_match_i,
    fence_i,
    mcountinhibit_q,
    mcycle,
    minstret,
    inst_ret,

    core_sleep_o,
    csr_access,
    csr_op,
    csr_addr,
    is_wfi,
    in_wfi,
    dpc_will_hit,
    addr_match,
    is_ebreak,
    is_cebreak,
    is_dret,
    is_mulhsu,
    pending_enabled_irq,
    pc_set,
    branch_in_ex;
  endclocking : mon_cb

endinterface : uvmt_cv32e40x_debug_cov_assert_if


// Exceptions interface

interface uvmt_cv32e40x_exceptions_if (
  input  clk_i,

  input  wb_valid,
  input  illegal_insn,

  output is_instr_illegal
);

  default clocking mon_cb @(posedge clk_i);
    default input #1step
  endclocking : mon_cb

endinterface : uvmt_cv32e40x_exceptions_if


`endif // __UVMT_CV32E40X_TB_IFS_SV__
