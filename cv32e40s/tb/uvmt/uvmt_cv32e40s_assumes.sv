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


  // Check: stalling is limited  (used for testing the assume)

  property p_obi_stall_limit (addr_ph_occurances, rsp_ph_occurances);
    logic [31:0]  new_count;

    ($changed(addr_ph_occurances), new_count = addr_ph_occurances)
    |=>
    ##[0:MAX_OBI_STALLS]  (rsp_ph_occurances == new_count);

    // Note: This property cannot be assumed because of lacking tool support
  endproperty : p_obi_stall_limit

  `ifdef OBI_STALL_RESTRICTIONS
    // TODO:silabs-robin ifdef used everywhere applicable
    a_obi_limit_instr_stalling: assert property (
      p_obi_stall_limit (
        sup.instr_bus_addr_ph_occurances,
        sup.instr_bus_rsp_ph_occurances
      )
    );

    a_obi_limit_data_stalling: assert property (
      p_obi_stall_limit (
        sup.data_bus_addr_ph_occurances,
        sup.data_bus_rsp_ph_occurances
      )
    );

    // TODO:silabs-robin instr/data for all assumes too
  `endif


  // Check: first N stalls are limited (used for testing the assume)

// TODO:silabs-robin for loop
  asu_obi_limit_instr_stalling: assume property (
    (sup.instr_bus_addr_ph_occurances == 1)
    |=>
    ##[0:MAX_OBI_STALLS]  (sup.instr_bus_rsp_ph_occurances == 1)
  );

/*
  asu_obi_limit_instr_stalling_2: assume property (
    (sup.instr_bus_addr_ph_occurances == 2)
    |=>
    ##[0:MAX_OBI_STALLS]  (sup.instr_bus_rsp_ph_occurances == 2)
  );
*/


  // Model elapsed cycles of stalled transactions

  logic [31:0]  instr_bus_outstanding;
  logic [31:0]  lapse_pointer_cur;
  logic [31:0]  lapse_pointer_prv;
  logic [31:0]  lapse_counter [MAX_OBI_STALLS];

  assign  instr_bus_outstanding =
    sup.instr_bus_addr_ph_occurances - sup.instr_bus_rsp_ph_occurances;

  assign  lapse_pointer_cur =
    $changed(sup.instr_bus_addr_ph_occurances)
      ? (lapse_pointer_prv + 1)
      : lapse_pointer_prv;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lapse_pointer_prv = 0;
    end else begin
      lapse_pointer_prv = lapse_pointer_cur;
    end
  end

  always_ff @(posedge clk_i) begin
    for (int i = 0; i < MAX_OBI_STALLS; i++) begin
      if (i < instr_bus_outstanding) begin
        int index = (lapse_pointer_cur - i) % MAX_OBI_STALLS;
        lapse_counter[index] <= lapse_counter[index] + 1;
      end
    end

    if ($changed(sup.instr_bus_addr_ph_occurances)) begin
      lapse_counter[lapse_pointer_cur] <= 1;
    end

    for (int i = 0; i < MAX_OBI_STALLS; i++) begin
      if (!rst_ni) begin
        lapse_counter[i] <= 0;
      end
    end

    // TODO:silabs-robin need to reset counters after events?
  end


  // Assume: stalling is limited

  for (genvar i = 0; i < MAX_OBI_STALLS; i++) begin
    a_limit_instr_2_max: assume property (
      !(
        instr_bus_outstanding  &&
        (lapse_counter[i] > MAX_OBI_STALLS)  &&
        !$changed(sup.instr_bus_rsp_ph_occurances)
      )
    );
    // Note: Has only been tested for a limit number of MAX_OBI_STALLS
  end


endmodule : uvmt_cv32e40s_assumes


`default_nettype  wire
