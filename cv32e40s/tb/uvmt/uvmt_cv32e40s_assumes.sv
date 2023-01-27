// Copyright 2023 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0.
//
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


`default_nettype  none


module  uvmt_cv32e40s_assumes (
  input wire  clk_i,
  input wire  rst_ni,

  uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.slave_mp  sup
);


  localparam logic [31:0]  MAX_OBI_STALLS = 8;


  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;


  property p_obi_limit_stalling (addr_ph_occurances, rsp_ph_occurances);
    logic [31:0]  new_count;

    ($changed(addr_ph_occurances), new_count = addr_ph_occurances)
    |=>
    ##[0:MAX_OBI_STALLS]  (rsp_ph_occurances == new_count);
  endproperty : p_obi_limit_stalling

  `ifdef OBI_STALL_RESTRICTIONS
    a_obi_limit_instr_stalling: assert property (
      p_obi_limit_stalling (sup.instr_bus_addr_ph_occurances, sup.instr_bus_rsp_ph_occurances)
    );

    a_obi_limit_data_stalling: assert property (
      p_obi_limit_stalling (sup.data_bus_addr_ph_occurances, sup.data_bus_rsp_ph_occurances)
    );

    // TODO:silabs-robin assume/restrict, not assert
  `endif


endmodule : uvmt_cv32e40s_assumes


`default_nettype  wire
