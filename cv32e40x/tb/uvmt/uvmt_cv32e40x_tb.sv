//
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//


`ifndef __UVMT_CV32E40X_TB_SV__
`define __UVMT_CV32E40X_TB_SV__


/**
 * Module encapsulating the CV32E40X DUT wrapper, and associated SV interfaces.
 * Also provide UVM environment entry and exit points.
 */
`default_nettype none
module uvmt_cv32e40x_tb;

   import uvm_pkg::*;
   import cv32e40x_pkg::*;
   import uvmt_cv32e40x_pkg::*;
   import uvme_cv32e40x_pkg::*;

   // CORE parameters
`ifdef SET_NUM_MHPMCOUNTERS
   parameter int CORE_PARAM_NUM_MHPMCOUNTERS = `SET_NUM_MHPMCOUNTERS;
`else
   parameter int CORE_PARAM_NUM_MHPMCOUNTERS = 1;
`endif
   // ENV (testbench) parameters
   parameter int ENV_PARAM_INSTR_ADDR_WIDTH  = 32;
   parameter int ENV_PARAM_INSTR_DATA_WIDTH  = 32;
   parameter int ENV_PARAM_RAM_ADDR_WIDTH    = 22;

   // Capture regs for test status from Virtual Peripheral in dut_wrap.mem_i
   bit        tp;
   bit        tf;
   bit        evalid;
   bit [31:0] evalue;

   // Agent interfaces
   uvma_isacov_if               isacov_if();
   uvma_clknrst_if              clknrst_if(); // clock and resets from the clknrst agent
   uvma_clknrst_if              clknrst_if_iss();
   uvma_debug_if                debug_if();
   uvma_interrupt_if            interrupt_if();
   uvma_obi_memory_if           obi_instr_if_i(
     .clk(clknrst_if.clk),
     .reset_n(clknrst_if.reset_n)
   );
   uvma_obi_memory_if           obi_data_if_i(
     .clk(clknrst_if.clk),
     .reset_n(clknrst_if.reset_n)
   );
   uvma_fencei_if               fencei_if_i(
     .clk(clknrst_if.clk),
     .reset_n(clknrst_if.reset_n)
   );

   // DUT Wrapper Interfaces
   uvmt_cv32e40x_vp_status_if       vp_status_if(.tests_passed(),
                                                 .tests_failed(),
                                                 .exit_valid(),
                                                 .exit_value()); // Status information generated by the Virtual Peripherals in the DUT WRAPPER memory.
   uvme_cv32e40x_core_cntrl_if      core_cntrl_if();
   uvmt_cv32e40x_core_status_if     core_status_if(.core_busy(),
                                                   .sec_lvl());     // Core status outputs

  /**
   * DUT WRAPPER instance:
   * This is an update of the riscv_wrapper.sv from PULP-Platform RI5CY project with
   * a few mods to bring unused ports from the CORE to this level using SV interfaces.
   */
   uvmt_cv32e40x_dut_wrap  #(
                             .NUM_MHPMCOUNTERS  (CORE_PARAM_NUM_MHPMCOUNTERS),
                             .B_EXT             (uvmt_cv32e40x_pkg::B_EXT),
                             .PMA_NUM_REGIONS   (uvmt_cv32e40x_pkg::CORE_PARAM_PMA_NUM_REGIONS),
                             .PMA_CFG           (uvmt_cv32e40x_pkg::CORE_PARAM_PMA_CFG),
                             .INSTR_ADDR_WIDTH  (ENV_PARAM_INSTR_ADDR_WIDTH),
                             .INSTR_RDATA_WIDTH (ENV_PARAM_INSTR_DATA_WIDTH),
                             .RAM_ADDR_WIDTH    (ENV_PARAM_RAM_ADDR_WIDTH)
                            )
                            dut_wrap (
                              .clknrst_if(clknrst_if),
                              .interrupt_if(interrupt_if),
                              .vp_status_if(vp_status_if),
                              .core_cntrl_if(core_cntrl_if),
                              .core_status_if(core_status_if),
                              .obi_instr_if_i(obi_instr_if_i),
                              .obi_data_if_i(obi_data_if_i),
                              .fencei_if_i(fencei_if_i),
                              .*);

  bind cv32e40x_wrapper
    uvma_rvfi_instr_if#(uvme_cv32e40x_pkg::ILEN,
                        uvme_cv32e40x_pkg::XLEN) rvfi_instr_if_0_i(.clk(clk_i),
                                                                   .reset_n(rst_ni),

                                                                   .rvfi_valid(rvfi_i.rvfi_valid[0]),
                                                                   .rvfi_order(rvfi_i.rvfi_order[uvma_rvfi_pkg::ORDER_WL*0+:uvma_rvfi_pkg::ORDER_WL]),
                                                                   .rvfi_insn(rvfi_i.rvfi_insn[uvme_cv32e40x_pkg::ILEN*0+:uvme_cv32e40x_pkg::ILEN]),
                                                                   .rvfi_trap(rvfi_i.rvfi_trap[0]),
                                                                   .rvfi_halt(rvfi_i.rvfi_halt[0]),
                                                                   .rvfi_intr(rvfi_i.rvfi_intr[0]),
                                                                   .rvfi_dbg(rvfi_i.rvfi_dbg),
                                                                   .rvfi_dbg_mode(rvfi_i.rvfi_dbg_mode),
                                                                   .rvfi_mode(rvfi_i.rvfi_mode[uvma_rvfi_pkg::MODE_WL*0+:uvma_rvfi_pkg::MODE_WL]),
                                                                   .rvfi_ixl(rvfi_i.rvfi_ixl[uvma_rvfi_pkg::IXL_WL*0+:uvma_rvfi_pkg::IXL_WL]),
                                                                   .rvfi_pc_rdata(rvfi_i.rvfi_pc_rdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_pc_wdata(rvfi_i.rvfi_pc_wdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_rs1_addr(rvfi_i.rvfi_rs1_addr[uvma_rvfi_pkg::GPR_ADDR_WL*0+:uvma_rvfi_pkg::GPR_ADDR_WL]),
                                                                   .rvfi_rs1_rdata(rvfi_i.rvfi_rs1_rdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_rs2_addr(rvfi_i.rvfi_rs2_addr[uvma_rvfi_pkg::GPR_ADDR_WL*0+:uvma_rvfi_pkg::GPR_ADDR_WL]),
                                                                   .rvfi_rs2_rdata(rvfi_i.rvfi_rs2_rdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_rs3_addr('0),
                                                                   .rvfi_rs3_rdata('0),
                                                                   .rvfi_rd1_addr(rvfi_i.rvfi_rd_addr[uvma_rvfi_pkg::GPR_ADDR_WL*0+:uvma_rvfi_pkg::GPR_ADDR_WL]),
                                                                   .rvfi_rd1_wdata(rvfi_i.rvfi_rd_wdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_rd2_addr('0),
                                                                   .rvfi_rd2_wdata('0),
                                                                   .rvfi_mem_addr(rvfi_i.rvfi_mem_addr[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_mem_rdata(rvfi_i.rvfi_mem_rdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_mem_rmask(rvfi_i.rvfi_mem_rmask[uvme_cv32e40x_pkg::XLEN/8*0+:uvme_cv32e40x_pkg::XLEN/8]),
                                                                   .rvfi_mem_wdata(rvfi_i.rvfi_mem_wdata[uvme_cv32e40x_pkg::XLEN*0+:uvme_cv32e40x_pkg::XLEN]),
                                                                   .rvfi_mem_wmask(rvfi_i.rvfi_mem_wmask[uvme_cv32e40x_pkg::XLEN/8*0+:uvme_cv32e40x_pkg::XLEN/8])
                                                                   );

  // RVFI CSR binds
  `RVFI_CSR_BIND(marchid)
  `RVFI_CSR_BIND(mcountinhibit)
  `RVFI_CSR_BIND(mstatus)
  `RVFI_CSR_BIND(mvendorid)
  `RVFI_CSR_BIND(misa)
  `RVFI_CSR_BIND(mtvec)
  `RVFI_CSR_BIND(mtval)
  `RVFI_CSR_BIND(mscratch)
  `RVFI_CSR_BIND(mepc)
  `RVFI_CSR_BIND(mcause)
  `RVFI_CSR_BIND(mip)
  `RVFI_CSR_BIND(mie)
  `RVFI_CSR_BIND(mhartid)
  `RVFI_CSR_BIND(mcontext)
  `RVFI_CSR_BIND(scontext)
  `RVFI_CSR_BIND(mimpid)
  `RVFI_CSR_BIND(minstret)
  `RVFI_CSR_BIND(minstreth)
  `RVFI_CSR_BIND(mcycle)
  `RVFI_CSR_BIND(mcycleh)

  `RVFI_CSR_BIND(dcsr)
  `RVFI_CSR_BIND(dpc)
  `RVFI_CSR_BIND(tselect)
  `RVFI_CSR_BIND(tinfo)

  `RVFI_CSR_IDX_BIND(mhpmcounter,,3)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,4)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,5)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,6)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,7)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,8)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,9)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,10)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,11)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,12)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,13)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,14)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,15)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,16)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,17)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,18)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,19)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,20)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,21)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,22)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,23)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,24)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,25)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,26)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,27)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,28)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,29)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,30)
  `RVFI_CSR_IDX_BIND(mhpmcounter,,31)

  `RVFI_CSR_IDX_BIND(mhpmevent,,3)
  `RVFI_CSR_IDX_BIND(mhpmevent,,4)
  `RVFI_CSR_IDX_BIND(mhpmevent,,5)
  `RVFI_CSR_IDX_BIND(mhpmevent,,6)
  `RVFI_CSR_IDX_BIND(mhpmevent,,7)
  `RVFI_CSR_IDX_BIND(mhpmevent,,8)
  `RVFI_CSR_IDX_BIND(mhpmevent,,9)
  `RVFI_CSR_IDX_BIND(mhpmevent,,10)
  `RVFI_CSR_IDX_BIND(mhpmevent,,11)
  `RVFI_CSR_IDX_BIND(mhpmevent,,12)
  `RVFI_CSR_IDX_BIND(mhpmevent,,13)
  `RVFI_CSR_IDX_BIND(mhpmevent,,14)
  `RVFI_CSR_IDX_BIND(mhpmevent,,15)
  `RVFI_CSR_IDX_BIND(mhpmevent,,16)
  `RVFI_CSR_IDX_BIND(mhpmevent,,17)
  `RVFI_CSR_IDX_BIND(mhpmevent,,18)
  `RVFI_CSR_IDX_BIND(mhpmevent,,19)
  `RVFI_CSR_IDX_BIND(mhpmevent,,20)
  `RVFI_CSR_IDX_BIND(mhpmevent,,21)
  `RVFI_CSR_IDX_BIND(mhpmevent,,22)
  `RVFI_CSR_IDX_BIND(mhpmevent,,23)
  `RVFI_CSR_IDX_BIND(mhpmevent,,24)
  `RVFI_CSR_IDX_BIND(mhpmevent,,25)
  `RVFI_CSR_IDX_BIND(mhpmevent,,26)
  `RVFI_CSR_IDX_BIND(mhpmevent,,27)
  `RVFI_CSR_IDX_BIND(mhpmevent,,28)
  `RVFI_CSR_IDX_BIND(mhpmevent,,29)
  `RVFI_CSR_IDX_BIND(mhpmevent,,30)
  `RVFI_CSR_IDX_BIND(mhpmevent,,31)

  `RVFI_CSR_IDX_BIND(mhpmcounter,h,3)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,4)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,5)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,6)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,7)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,8)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,9)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,10)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,11)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,12)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,13)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,14)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,15)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,16)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,17)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,18)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,19)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,20)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,21)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,22)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,23)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,24)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,25)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,26)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,27)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,28)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,29)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,30)
  `RVFI_CSR_IDX_BIND(mhpmcounter,h,31)

  // dscratch0
  bind cv32e40x_wrapper
    uvma_rvfi_csr_if#(uvme_cv32e40x_pkg::XLEN) rvfi_csr_dscratch0_if_0_i(.clk(clk_i),
                                                                         .reset_n(rst_ni),
                                                                         .rvfi_csr_rmask(rvfi_i.rvfi_csr_dscratch_rmask[0]),
                                                                         .rvfi_csr_wmask(rvfi_i.rvfi_csr_dscratch_wmask[0]),
                                                                         .rvfi_csr_rdata(rvfi_i.rvfi_csr_dscratch_rdata[0]),
                                                                         .rvfi_csr_wdata(rvfi_i.rvfi_csr_dscratch_wdata[0])
    );

  // dscratch1
  bind cv32e40x_wrapper
    uvma_rvfi_csr_if#(uvme_cv32e40x_pkg::XLEN) rvfi_csr_dscratch1_if_0_i(.clk(clk_i),
                                                                         .reset_n(rst_ni),
                                                                         .rvfi_csr_rmask(rvfi_i.rvfi_csr_dscratch_rmask[1]),
                                                                         .rvfi_csr_wmask(rvfi_i.rvfi_csr_dscratch_wmask[1]),
                                                                         .rvfi_csr_rdata(rvfi_i.rvfi_csr_dscratch_rdata[1]),
                                                                         .rvfi_csr_wdata(rvfi_i.rvfi_csr_dscratch_wdata[1])
    );

  // tdata1
  bind cv32e40x_wrapper
    uvma_rvfi_csr_if#(uvme_cv32e40x_pkg::XLEN) rvfi_csr_tdata1_if_0_i(.clk(clk_i),
                                                                     .reset_n(rst_ni),
                                                                     .rvfi_csr_rmask(rvfi_i.rvfi_csr_tdata_rmask[1]),
                                                                     .rvfi_csr_wmask(rvfi_i.rvfi_csr_tdata_wmask[1]),
                                                                     .rvfi_csr_rdata(rvfi_i.rvfi_csr_tdata_rdata[1]),
                                                                     .rvfi_csr_wdata(rvfi_i.rvfi_csr_tdata_wdata[1])
    );

  // tdata2
  bind cv32e40x_wrapper
    uvma_rvfi_csr_if#(uvme_cv32e40x_pkg::XLEN) rvfi_csr_tdata2_if_0_i(.clk(clk_i),
                                                                     .reset_n(rst_ni),
                                                                     .rvfi_csr_rmask(rvfi_i.rvfi_csr_tdata_rmask[2]),
                                                                     .rvfi_csr_wmask(rvfi_i.rvfi_csr_tdata_wmask[2]),
                                                                     .rvfi_csr_rdata(rvfi_i.rvfi_csr_tdata_rdata[2]),
                                                                     .rvfi_csr_wdata(rvfi_i.rvfi_csr_tdata_wdata[2])
    );

  // tdata3
  bind cv32e40x_wrapper
    uvma_rvfi_csr_if#(uvme_cv32e40x_pkg::XLEN) rvfi_csr_tdata3_if_0_i(.clk(clk_i),
                                                                     .reset_n(rst_ni),
                                                                     .rvfi_csr_rmask(rvfi_i.rvfi_csr_tdata_rmask[3]),
                                                                     .rvfi_csr_wmask(rvfi_i.rvfi_csr_tdata_wmask[3]),
                                                                     .rvfi_csr_rdata(rvfi_i.rvfi_csr_tdata_rdata[3]),
                                                                     .rvfi_csr_wdata(rvfi_i.rvfi_csr_tdata_wdata[3])
    );

  bind uvmt_cv32e40x_dut_wrap
    uvma_obi_memory_assert_if_wrp#(
      .ADDR_WIDTH(32),
      .DATA_WIDTH(32),
      .AUSER_WIDTH(0),
      .WUSER_WIDTH(0),
      .RUSER_WIDTH(0),
      .ID_WIDTH(0),
      .ACHK_WIDTH(0),
      .RCHK_WIDTH(0),
      .IS_1P2(1)
    ) obi_instr_memory_assert_i(.obi(obi_instr_if_i));

  bind uvmt_cv32e40x_dut_wrap
    uvma_obi_memory_assert_if_wrp#(
      .ADDR_WIDTH(32),
      .DATA_WIDTH(32),
      .AUSER_WIDTH(0),
      .WUSER_WIDTH(0),
      .RUSER_WIDTH(0),
      .ID_WIDTH(0),
      .ACHK_WIDTH(0),
      .RCHK_WIDTH(0),
      .IS_1P2(1)
    ) obi_data_memory_assert_i(.obi(obi_data_if_i));

  // Bind in verification modules to the design
  bind cv32e40x_core
    uvmt_cv32e40x_interrupt_assert interrupt_assert_i(.mcause_n({cs_registers_i.mcause_n.interrupt, cs_registers_i.mcause_n.exception_code[4:0]}),
                                                      .mip(cs_registers_i.mip),
                                                      .mie_q(cs_registers_i.mie_q),
                                                      .mstatus_mie(cs_registers_i.mstatus_q.mie),
                                                      .mtvec_mode_q(cs_registers_i.mtvec_q.mode),
                                                      .if_stage_instr_rvalid_i(if_stage_i.m_c_obi_instr_if.s_rvalid.rvalid),
                                                      .if_stage_instr_rdata_i(if_stage_i.m_c_obi_instr_if.resp_payload.rdata),
                                                      .id_stage_instr_valid_i(wb_stage_i.instr_valid),
                                                      .id_stage_instr_rdata_i(wb_stage_i.ex_wb_pipe_i.instr.bus_resp.rdata),
                                                      .branch_taken_ex(controller_i.controller_fsm_i.branch_taken_ex),
                                                      .debug_mode_q(controller_i.controller_fsm_i.debug_mode_q),
                                                      .irq_ack_o(core_i.irq_ack),
                                                      .irq_id_o(core_i.irq_id),
                                                      .*);

  // Fence.i assertions

  bind cv32e40x_wrapper
    uvmt_cv32e40x_fencei_assert  fencei_assert_i (
      .wb_valid (core_i.wb_stage_i.wb_valid),
      .wb_instr_valid (core_i.ex_wb_pipe.instr_valid),
      .wb_fencei_insn (core_i.ex_wb_pipe.fencei_insn),
      .wb_pc (core_i.ex_wb_pipe.pc),
      .wb_rdata (core_i.ex_wb_pipe.instr.bus_resp.rdata),

      .rvfi_valid (rvfi_i.rvfi_valid),
      .rvfi_intr (rvfi_i.rvfi_intr),
      .rvfi_dbg_mode (rvfi_i.rvfi_dbg_mode),

      .*
    );

  // NMI assertions

  bind cv32e40x_wrapper
    uvmt_cv32e40x_nmi_assert  nmi_assert_i (
      .pending_nmi (core_i.controller_i.controller_fsm_i.pending_nmi),
      .nmi_allowed (core_i.controller_i.controller_fsm_i.nmi_allowed),

      .rvfi_valid (rvfi_i.rvfi_valid),
      .rvfi_csr_mcause_rdata (rvfi_i.rvfi_csr_mcause_rdata),
      .rvfi_csr_mcause_rmask (rvfi_i.rvfi_csr_mcause_rmask),
      .rvfi_csr_mcause_wdata (rvfi_i.rvfi_csr_mcause_wdata),
      .rvfi_csr_mcause_wmask (rvfi_i.rvfi_csr_mcause_wmask),

      .nmi_addr_i (core_i.nmi_addr_i),
      .fetch_enable_i (core_i.fetch_enable_i),

      .*
    );


  // Debug assertion and coverage interface

  // Instantiate debug assertions

  bind cv32e40x_wrapper
    uvmt_cv32e40x_debug_cov_assert_if debug_cov_assert_if (
      .id_valid(core_i.id_stage_i.id_valid_o),
      .ex_stage_csr_en(core_i.id_ex_pipe.csr_en),
      .ex_valid(core_i.ex_stage_i.instr_valid),
      .ex_stage_instr_rdata_i(core_i.id_ex_pipe.instr.bus_resp.rdata),
      .ex_stage_pc(core_i.id_ex_pipe.pc),
      .wb_stage_instr_rdata_i(core_i.ex_wb_pipe.instr.bus_resp.rdata),
      .wb_stage_instr_valid_i(core_i.ex_wb_pipe.instr_valid),
      .wb_stage_pc           (core_i.wb_stage_i.ex_wb_pipe_i.pc),
      .wb_err                (core_i.ex_wb_pipe.instr.bus_resp.err),
      .mie_q(core_i.cs_registers_i.mie_q),
      .ctrl_fsm_cs(core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
      .illegal_insn_i(core_i.ex_wb_pipe.illegal_insn),
      .wb_illegal(core_i.ex_wb_pipe.illegal_insn),
      .wb_valid(core_i.wb_stage_i.wb_valid_o),
      .ecall_insn_i(core_i.ex_wb_pipe.ecall_insn),
      .debug_req_i(core_i.controller_i.controller_fsm_i.debug_req_i),
      .debug_req_q(core_i.controller_i.controller_fsm_i.debug_req_q),
      .pending_debug(core_i.controller_i.controller_fsm_i.pending_debug),
      .debug_mode_q(core_i.controller_i.controller_fsm_i.debug_mode_q),
      .dcsr_q(core_i.cs_registers_i.dcsr_q),
      .depc_q(core_i.cs_registers_i.dpc_q),
      .depc_n(core_i.cs_registers_i.dpc_n),
      .mcause_q({core_i.cs_registers_i.mcause_q[31], core_i.cs_registers_i.mcause_q[4:0]}),
      .mtvec(core_i.cs_registers_i.mtvec_q),
      .mepc_q(core_i.cs_registers_i.mepc_q),
      .tdata1(core_i.cs_registers_i.tmatch_control_q),
      .tdata2(core_i.cs_registers_i.tmatch_value_q),
      .trigger_match_i(core_i.controller_i.controller_fsm_i.trigger_match_in_wb),  // TODO:ropeders
      .mcountinhibit_q(core_i.cs_registers_i.mcountinhibit_q),
      .mcycle(core_i.cs_registers_i.mhpmcounter_q[0]),
      .minstret(core_i.cs_registers_i.mhpmcounter_q[2]),
      .fence_i(core_i.id_stage_i.decoder_i.fencei_insn_o),
      // TODO: review this change from CV32E40X_HASH f6196bf to a26b194. It should be logically equivalent.
      //assign debug_cov_assert_if.inst_ret = core_i.cs_registers_i.inst_ret;
      // First attempt: this causes unexpected failures of a_minstret_count
      //assign debug_cov_assert_if.inst_ret = (core_i.id_valid &
      //                                       core_i.is_decoding);
      // Second attempt: (based on OK input).  This passes, but maybe only because p_minstret_count
      //                                       is the only property sensitive to inst_ret. Will
      //                                       this work in the general case?
      .inst_ret(core_i.ctrl_fsm.mhpmevent.minstret),
      .csr_access(core_i.ex_wb_pipe.csr_en),
      .csr_op(core_i.ex_wb_pipe.csr_op),
      .csr_addr(core_i.ex_wb_pipe.csr_addr),
      .csr_we_int(core_i.cs_registers_i.csr_we_int),
      .irq_ack_o(core_i.irq_ack),
      .irq_id_o(core_i.irq_id),
      .dm_halt_addr_i(core_i.dm_halt_addr_i),
      .dm_exception_addr_i(core_i.dm_exception_addr_i),
      .core_sleep_o(core_i.core_sleep_o),
      .irq_i(core_i.irq_i),
      .pc_set(core_i.ctrl_fsm.pc_set),
      .boot_addr_i(core_i.boot_addr_i),
      .branch_in_ex(core_i.controller_i.controller_fsm_i.branch_in_ex),

      .rvfi_valid(rvfi_i.rvfi_valid),
      .rvfi_pc_wdata(rvfi_i.rvfi_pc_wdata),
      .rvfi_pc_rdata(rvfi_i.rvfi_pc_rdata),

      .is_wfi(),
      .in_wfi(),
      .dpc_will_hit(),
      .addr_match(),
      .is_ebreak(),
      .is_cebreak(),
      .is_dret(),
      .is_mulhsu(),
      .pending_enabled_irq(),

      .*
    );

    bind cv32e40x_wrapper uvmt_cv32e40x_debug_assert u_debug_assert(.cov_assert_if(debug_cov_assert_if));

    //uvmt_cv32e40x_rvvi_handcar u_rvvi_handcar();
    /**
    * ISS WRAPPER instance:
    */
      uvmt_cv32e40x_iss_wrap  #(
                                .ID (0),
                                .ROM_START_ADDR('h0),
                                .ROM_BYTE_SIZE('h0),
                                .RAM_BYTE_SIZE('h1_0000_0000)
                               )
                               iss_wrap ( .clk_period(clknrst_if.clk_period),
                                          .clknrst_if(clknrst_if_iss)
                                 );

      assign clknrst_if_iss.reset_n = clknrst_if.reset_n;

   /**
    * Test bench entry point.
    */
   initial begin : test_bench_entry_point

     // Specify time format for simulation (units_number, precision_number, suffix_string, minimum_field_width)
     $timeformat(-9, 3, " ns", 8);

     // Add interfaces handles to uvm_config_db
     uvm_config_db#(virtual uvma_isacov_if              )::set(.cntxt(null), .inst_name("*.env.isacov_agent"), .field_name("vif"), .value(isacov_if));
     uvm_config_db#(virtual uvma_debug_if               )::set(.cntxt(null), .inst_name("*.env.debug_agent"), .field_name("vif"), .value(debug_if));
     uvm_config_db#(virtual uvma_clknrst_if             )::set(.cntxt(null), .inst_name("*.env.clknrst_agent"), .field_name("vif"),        .value(clknrst_if));
     uvm_config_db#(virtual uvma_interrupt_if           )::set(.cntxt(null), .inst_name("*.env.interrupt_agent"), .field_name("vif"),      .value(interrupt_if));
     uvm_config_db#(virtual uvma_obi_memory_if          )::set(.cntxt(null), .inst_name("*.env.obi_memory_instr_agent"), .field_name("vif"), .value(obi_instr_if_i) );
     uvm_config_db#(virtual uvma_obi_memory_if          )::set(.cntxt(null), .inst_name("*.env.obi_memory_data_agent"),  .field_name("vif"), .value(obi_data_if_i) );
     uvm_config_db#(virtual uvma_fencei_if              )::set(.cntxt(null), .inst_name("*.env.fencei"),     .field_name("vif"), .value(fencei_if_i));
     uvm_config_db#(virtual uvma_rvfi_instr_if          )::set(.cntxt(null), .inst_name("*.env.rvfi_agent"), .field_name("instr_vif0"),.value(dut_wrap.cv32e40x_wrapper_i.rvfi_instr_if_0_i));
     uvm_config_db#(virtual uvma_fencei_if              )::set(.cntxt(null), .inst_name("*.env.fencei_agent"), .field_name("fencei_vif"),     .value(fencei_if_i)  );
     uvm_config_db#(virtual uvmt_cv32e40x_vp_status_if  )::set(.cntxt(null), .inst_name("*"),                .field_name("vp_status_vif"),    .value(vp_status_if) );
     uvm_config_db#(virtual uvma_interrupt_if           )::set(.cntxt(null), .inst_name("*.env"),            .field_name("intr_vif"),         .value(interrupt_if) );
     uvm_config_db#(virtual uvma_debug_if               )::set(.cntxt(null), .inst_name("*.env"),            .field_name("debug_vif"),        .value(debug_if)     );
//     uvm_config_db#(virtual uvmt_cv32e40x_debug_cov_assert_if)::set(.cntxt(null), .inst_name("*.env"),       .field_name("debug_cov_vif"),    .value(debug_cov_assert_if));
     `RVFI_CSR_UVM_CONFIG_DB_SET(marchid)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mcountinhibit)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mstatus)
     `RVFI_CSR_UVM_CONFIG_DB_SET(misa)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mtvec)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mtval)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mvendorid)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mscratch)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mepc)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mcause)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mip)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mie)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhartid)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mimpid)
     `RVFI_CSR_UVM_CONFIG_DB_SET(minstret)
     `RVFI_CSR_UVM_CONFIG_DB_SET(minstreth)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mcontext)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mcycle)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mcycleh)

     `RVFI_CSR_UVM_CONFIG_DB_SET(dcsr)
     `RVFI_CSR_UVM_CONFIG_DB_SET(dpc)
     `RVFI_CSR_UVM_CONFIG_DB_SET(dscratch0)
     `RVFI_CSR_UVM_CONFIG_DB_SET(dscratch1)
     `RVFI_CSR_UVM_CONFIG_DB_SET(scontext)
     `RVFI_CSR_UVM_CONFIG_DB_SET(tselect)
     `RVFI_CSR_UVM_CONFIG_DB_SET(tdata1)
     `RVFI_CSR_UVM_CONFIG_DB_SET(tdata2)
     `RVFI_CSR_UVM_CONFIG_DB_SET(tdata3)
     `RVFI_CSR_UVM_CONFIG_DB_SET(tinfo)

     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent3)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent4)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent5)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent6)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent7)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent8)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent9)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent10)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent11)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent12)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent13)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent14)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent15)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent16)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent17)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent18)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent19)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent20)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent21)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent22)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent23)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent24)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent25)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent26)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent27)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent28)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent29)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent30)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmevent31)

     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter3)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter4)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter5)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter6)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter7)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter8)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter9)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter10)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter11)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter12)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter13)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter14)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter15)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter16)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter17)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter18)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter19)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter20)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter21)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter22)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter23)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter24)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter25)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter26)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter27)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter28)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter29)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter30)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter31)

     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter3h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter4h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter5h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter6h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter7h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter8h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter9h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter10h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter11h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter12h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter13h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter14h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter15h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter16h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter17h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter18h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter19h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter20h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter21h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter22h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter23h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter24h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter25h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter26h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter27h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter28h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter29h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter30h)
     `RVFI_CSR_UVM_CONFIG_DB_SET(mhpmcounter31h)

     uvm_config_db#(virtual RVVI_state#(.ILEN(uvme_cv32e40x_pkg::ILEN),
                                        .XLEN(uvme_cv32e40x_pkg::XLEN)
                                        ))::set(.cntxt(null), .inst_name("*.env.rvvi_agent"), .field_name("state_vif"), .value(iss_wrap.cpu.state));
     uvm_config_db#(virtual RVVI_control                )::set(.cntxt(null), .inst_name("*.env.rvvi_agent"), .field_name("control_vif"), .value(iss_wrap.cpu.control));
     uvm_config_db#(virtual RVVI_bus                    )::set(.cntxt(null), .inst_name("*.env.rvvi_agent"), .field_name("ovpsim_bus_vif"), .value(iss_wrap.bus));
     uvm_config_db#(virtual RVVI_io                     )::set(.cntxt(null), .inst_name("*.env.rvvi_agent"), .field_name("ovpsim_io_vif"), .value(iss_wrap.io));
     uvm_config_db#(virtual RVVI_memory                 )::set(.cntxt(null), .inst_name("*.env.rvvi_agent"), .field_name("ovpsim_mem_vif"), .value(iss_wrap.ram.memory));
     uvm_config_db#(virtual uvmt_cv32e40x_vp_status_if      )::set(.cntxt(null), .inst_name("*"), .field_name("vp_status_vif"),       .value(vp_status_if)      );
     uvm_config_db#(virtual uvme_cv32e40x_core_cntrl_if     )::set(.cntxt(null), .inst_name("*"), .field_name("core_cntrl_vif"),      .value(core_cntrl_if)     );
     uvm_config_db#(virtual uvmt_cv32e40x_core_status_if    )::set(.cntxt(null), .inst_name("*"), .field_name("core_status_vif"),     .value(core_status_if)    );
     uvm_config_db#(virtual uvmt_cv32e40x_debug_cov_assert_if)::set(.cntxt(null), .inst_name("*.env"), .field_name("debug_cov_vif"),.value(dut_wrap.cv32e40x_wrapper_i.debug_cov_assert_if));

     // Make the DUT Wrapper Virtual Peripheral's status outputs available to the base_test
     uvm_config_db#(bit      )::set(.cntxt(null), .inst_name("*"), .field_name("tp"),     .value(1'b0)        );
     uvm_config_db#(bit      )::set(.cntxt(null), .inst_name("*"), .field_name("tf"),     .value(1'b0)        );
     uvm_config_db#(bit      )::set(.cntxt(null), .inst_name("*"), .field_name("evalid"), .value(1'b0)        );
     uvm_config_db#(bit[31:0])::set(.cntxt(null), .inst_name("*"), .field_name("evalue"), .value(32'h00000000));

	 // DUT and ENV parameters
     uvm_config_db#(int)::set(.cntxt(null), .inst_name("*"), .field_name("CORE_PARAM_NUM_MHPMCOUNTERS"), .value(CORE_PARAM_NUM_MHPMCOUNTERS));
     uvm_config_db#(int)::set(.cntxt(null), .inst_name("*"), .field_name("ENV_PARAM_INSTR_ADDR_WIDTH"),  .value(ENV_PARAM_INSTR_ADDR_WIDTH) );
     uvm_config_db#(int)::set(.cntxt(null), .inst_name("*"), .field_name("ENV_PARAM_INSTR_DATA_WIDTH"),  .value(ENV_PARAM_INSTR_DATA_WIDTH) );
     uvm_config_db#(int)::set(.cntxt(null), .inst_name("*"), .field_name("ENV_PARAM_RAM_ADDR_WIDTH"),    .value(ENV_PARAM_RAM_ADDR_WIDTH)   );

     // Run test
     uvm_top.enable_print_topology = 0; // ENV coders enable this as a debug aid
     uvm_top.finish_on_completion  = 1;
     uvm_top.run_test();
   end : test_bench_entry_point

   assign core_cntrl_if.clk = clknrst_if.clk;

   // Informational print message on loading of OVPSIM ISS to benchmark some elf image loading times
   // OVPSIM runs its initialization at the #1ns timestamp, and should dominate the initial startup time
   longint start_ovpsim_init_time;
   longint end_ovpsim_init_time;
   initial begin
      if (!$test$plusargs("DISABLE_OVPSIM")) begin
        #0.9ns;
        `uvm_info("OVPSIM", $sformatf("Start benchmarking OVPSIM initialization"), UVM_LOW)
        start_ovpsim_init_time = svlib_pkg::sys_dayTime();
        #1.1ns;
        end_ovpsim_init_time = svlib_pkg::sys_dayTime();
        `uvm_info("OVPSIM", $sformatf("Initialization time: %0d seconds", end_ovpsim_init_time - start_ovpsim_init_time), UVM_LOW)
      end
    end

   //TODO verify these are correct with regards to isacov function
   always @(dut_wrap.cv32e40x_wrapper_i.rvfi_instr_if_0_i.rvfi_valid) -> isacov_if.retire;
   assign isacov_if.instr = dut_wrap.cv32e40x_wrapper_i.rvfi_instr_if_0_i.rvfi_insn;
   //assign isacov_if.is_compressed = dut_wrap.cv32e40x_wrapper_i.tracer_i.insn_compressed;

   // Capture the test status and exit pulse flags
   // TODO: put this logic in the vp_status_if (makes it easier to pass to ENV)
   always @(posedge clknrst_if.clk) begin
     if (!clknrst_if.reset_n) begin
       tp     <= 1'b0;
       tf     <= 1'b0;
       evalid <= 1'b0;
       evalue <= 32'h00000000;
     end
     else begin
       if (vp_status_if.tests_passed) begin
         tp <= 1'b1;
         uvm_config_db#(bit)::set(.cntxt(null), .inst_name("*"), .field_name("tp"), .value(1'b1));
       end
       if (vp_status_if.tests_failed) begin
         tf <= 1'b1;
         uvm_config_db#(bit)::set(.cntxt(null), .inst_name("*"), .field_name("tf"), .value(1'b1));
       end
       if (vp_status_if.exit_valid) begin
         evalid <= 1'b1;
         uvm_config_db#(bit)::set(.cntxt(null), .inst_name("*"), .field_name("evalid"), .value(1'b1));
       end
       if (vp_status_if.exit_valid) begin
         evalue <= vp_status_if.exit_value;
         uvm_config_db#(bit[31:0])::set(.cntxt(null), .inst_name("*"), .field_name("evalue"), .value(vp_status_if.exit_value));
       end
     end
   end


   /**
    * End-of-test summary printout.
    */
   final begin: end_of_test
      string             summary_string;
      uvm_report_server  rs;
      int                err_count;
      int                warning_count;
      int                fatal_count;
      static bit         sim_finished = 0;

      static string  red   = "\033[31m\033[1m";
      static string  green = "\033[32m\033[1m";
      static string  reset = "\033[0m";

      rs            = uvm_top.get_report_server();
      err_count     = rs.get_severity_count(UVM_ERROR);
      warning_count = rs.get_severity_count(UVM_WARNING);
      fatal_count   = rs.get_severity_count(UVM_FATAL);

      void'(uvm_config_db#(bit)::get(null, "", "sim_finished", sim_finished));

      $display("\n%m: *** Test Summary ***\n");

      if (sim_finished && (err_count == 0) && (fatal_count == 0)) begin
         $display("    PPPPPPP    AAAAAA    SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
         $display("    PP    PP  AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
         $display("    PP    PP  AA    AA  SS        SS        EE        DD    DD    ");
         $display("    PPPPPPP   AAAAAAAA   SSSSSS    SSSSSS   EEEEE     DD    DD    ");
         $display("    PP        AA    AA        SS        SS  EE        DD    DD    ");
         $display("    PP        AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
         $display("    PP        AA    AA   SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
         $display("    ----------------------------------------------------------");
         if (warning_count == 0) begin
           $display("                        SIMULATION PASSED                     ");
         end
         else begin
           $display("                 SIMULATION PASSED with WARNINGS              ");
         end
         $display("    ----------------------------------------------------------");
      end
      else begin
         $display("    FFFFFFFF   AAAAAA   IIIIII  LL        EEEEEEEE  DDDDDDD       ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FFFFF     AAAAAAAA    II    LL        EEEEE     DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA  IIIIII  LLLLLLLL  EEEEEEEE  DDDDDDD       ");

         if (sim_finished == 0) begin
            $display("    --------------------------------------------------------");
            $display("                   SIMULATION FAILED - ABORTED              ");
            $display("    --------------------------------------------------------");
         end
         else begin
            $display("    --------------------------------------------------------");
            $display("                       SIMULATION FAILED                    ");
            $display("    --------------------------------------------------------");
         end
      end
   end

endmodule : uvmt_cv32e40x_tb
`default_nettype wire

`endif // __UVMT_CV32E40X_TB_SV__
