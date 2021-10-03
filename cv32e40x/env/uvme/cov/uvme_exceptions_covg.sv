// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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


`uvm_analysis_imp_decl(_rvfi)


covergroup cg_rvfi
  with function sample(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) rvfi);

  `per_instance_fcov

  cp_trap : coverpoint rvfi.trap {
    bins rvfi_trap = {1};
  }
  cp_intr : coverpoint rvfi.intr {
    bins rvfi_intr = {1};
  }
  cp_imm12 : coverpoint rvfi.insn[31:20] {
    option.auto_bin_max = 4096;
  }
  cp_is_csr : coverpoint ((rvfi.insn[6:0] == 7'b 1110011) && (rvfi.insn[13:12] != 2'b 00)) {
    bins is_csr = {1};
  }
  cp_is_ebreak : coverpoint (rvfi.insn inside {32'h 00100073, 32'h 9002}) {
    bins is_ebreak = {1};
  }
  cp_no_ebreakm : coverpoint (rvfi.csrs["dcsr"].get_csr_retirement_data()[15]) {
    bins no_ebreakm = {0};
  }
  cp_mcause : coverpoint rvfi.csrs["mcause"].get_csr_retirement_data() {
    bins reset               = {0};
    bins ins_acc_fault       = {1};
    bins illegal_ins         = {2};
    bins breakpoint          = {3};
    bins load_acc_fault      = {5};
    bins store_amo_acc_fault = {7};
    bins ecall               = {11};
    bins ins_bus_fault       = {48};
  }
  cp_pcr_mtvec : coverpoint (rvfi.pc_rdata[31:2] == rvfi.csrs["mtvec"].get_csr_retirement_data()[31:2]) {
    bins one = {1};
  }
  cp_pcw_mtvec : coverpoint (rvfi.pc_wdata[31:2] == rvfi.csrs["mtvec"].get_csr_retirement_data()[31:2]) {
    bins one = {1};
  }
  // TODO:ropeders mepc
  // TODO:ropeders mtval
  // TODO:ropeders all other covers

  // TODO:ropeders all crosses
  x_all_csrs : cross cp_imm12, cp_is_csr;  // CSR instructions shall try all 2^12 existing/nonexisting CSRs
  x_trap_to_mtvec : cross cp_trap, cp_pcw_mtvec;  // Trap going to mtvec.base
  x_trap_in_mtvec : cross cp_intr, cp_pcr_mtvec;  // Trap executing at mtvec.base
  x_ebreak_trap : cross cp_is_ebreak, cp_no_ebreakm, cp_trap, cp_mcause {
    ignore_bins ig = ! binsof(cp_mcause) intersect {3};  // Shall hit specifically mcause == breakpoint
  }
  x_trap_mcause : cross cp_trap, cp_mcause {
    ignore_bins ig = binsof(cp_mcause) intersect {0};  // Can't trap with mcause == reset value
  }
  x_intr_mcause : cross cp_intr, cp_mcause {
    ignore_bins ig = binsof(cp_mcause) intersect {0};  // Can't trap with mcause == reset value
  }

endgroup : cg_rvfi


covergroup cg_vif
  with function sample(virtual uvmt_cv32e40x_exceptions_if  vif);

  `per_instance_fcov

  // TODO cp_ibus_breakpoint_addr;
  // TODO cp_ibus_pma;
  // TODO cp_ibus_buserr;
  cp_instr_illegal: coverpoint vif.is_instr_illegal;
  // TODO cp_instr_ecall;
  // TODO cp_instr_ebreak;
  // TODO cp_dbus_breakpoint_addr;
  // TODO cp_dbus_breakpoint_data;
  // TODO cp_dbus_pma_store_misaligned;
  // TODO cp_dbus_pma_store_amo;
  // TODO cp_dbus_pma_store_conditional;
  // TODO cp_dbus_pma_load_misaligned;
  // TODO cp_dbus_pma_load_reserved;

  // TODO crosses

endgroup : cg_vif;


class uvme_exceptions_covg extends uvm_component;

  uvme_cv32e40x_cntxt_c  cntxt;
  cg_rvfi  rvfi_cg;
  cg_vif  vif_cg;
  uvm_analysis_imp_rvfi#(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN), uvme_exceptions_covg)  rvfi_mon_export;

  `uvm_component_utils(uvme_exceptions_covg);

  extern function new(string name = "exceptions_covg", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) trn);

endclass : uvme_exceptions_covg


function uvme_exceptions_covg::new(string name = "exceptions_covg", uvm_component parent = null);

  super.new(name, parent);

  rvfi_mon_export = new("rvfi_mon_export", this);

endfunction : new


function void uvme_exceptions_covg::build_phase(uvm_phase phase);

  super.build_phase(phase);

  rvfi_cg = new();
  vif_cg = new();

  void'(uvm_config_db#(uvme_cv32e40x_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (cntxt == null) `uvm_fatal("EXCEPTIONSCOVG", "No cntxt object passed to model");

endfunction : build_phase


task uvme_exceptions_covg::run_phase(uvm_phase phase);

  super.run_phase(phase);

  while (1) begin
    @(cntxt.exceptions_vif.mon_cb);
    vif_cg.sample(cntxt.exceptions_vif);
  end

endtask : run_phase


function void uvme_exceptions_covg::write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) trn);

  rvfi_cg.sample(trn);

endfunction : write_rvfi
