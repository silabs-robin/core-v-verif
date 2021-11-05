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

  input pending_nmi,
  input nmi_allowed
);

  default clocking cb @(posedge clk_i); endclocking
  string info_tag = "CV32E40X_NMI_ASSERT";

  a_rvfi_intr: assert property (
    pending_nmi && nmi_allowed
    |->
    1  // TODO:ropeders
  ) else `uvm_error(info_tag, "TODO");

endmodule : uvmt_cv32e40x_nmi_assert
