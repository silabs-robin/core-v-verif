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


module uvmt_cv32e40x_nmi_assert
  import uvm_pkg::*;
(
  input clk_i,
  input rst_ni,

  // Controller signals
  input pending_nmi,
  input nmi_allowed,

  // RVFI signals
  input        rvfi_valid,
  input [31:0] rvfi_csr_mcause_rdata,

  // Core signals
  input [31:0] nmi_addr_i,
  input        fetch_enable_i
);

  default clocking cb @(posedge clk_i); endclocking
  string info_tag = "CV32E40X_NMI_ASSERT";

  sequence s_rvfi_intr_ante;
    pending_nmi && nmi_allowed
    ##1 rvfi_valid[->1];
  endsequence
  a_rvfi_intr: assert property (
    s_rvfi_intr_ante
    |->
    1 //TODO
  ) else `uvm_error(info_tag, "rvfi did not signal 'intr' upon entering nmi handler");
  c_rvfi_intr_load: cover property (s_rvfi_intr_ante ##0 (rvfi_csr_mcause_rdata == 32'h 8000_0080));
  c_rvfi_intr_store: cover property (s_rvfi_intr_ante ##0 (rvfi_csr_mcause_rdata == 32'h 8000_0081));

  a_addr_stable: assert property (
    fetch_enable_i
    |=>
    $stable(nmi_addr_i)
  ) else `uvm_error(info_tag, "TODO");

endmodule : uvmt_cv32e40x_nmi_assert
