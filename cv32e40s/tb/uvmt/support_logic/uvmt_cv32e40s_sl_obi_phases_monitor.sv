// Copyright 2022 Silicon Labs, Inc.
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


module uvmt_cv32e40s_sl_obi_phases_monitor
  import uvm_pkg::*;
  (
    input logic clk_i,
    input logic rst_ni,

    input logic obi_req,
    input logic obi_gnt,
    input logic obi_rvalid,


    // continued address and respons phase indicators, indicates address and respons phases
    // of more than one cycle
    output logic addr_ph_cont,
    output logic resp_ph_cont,

    // outstanding transaction counter, used to verify no response phase preceedes an address phase
    output integer v_addr_ph_cnt,

    output [31:0]  addr_ph_occurances,
    output [31:0]  rsp_ph_occurances
  );

  logic addr_ph_valid;
  logic rsp_ph_valid;
  logic obi_rready;

  logic [31:0] addr_ph_lapse_comb;
  logic [31:0] addr_ph_lapse_ff;
  logic        addr_ph_occured;

  logic [31:0] addr_ph_occurances_ff;
  logic [31:0] rsp_ph_occurances_ff;
  logic [31:0] addr_ph_occurances_comb;
  logic [31:0] rsp_ph_occurances_comb;


  assign obi_rready = 1'b1;  // Note: This is an assumption

  assign addr_ph_valid = obi_req == 1'b1 && obi_gnt == 1'b1;
  assign rsp_ph_valid = obi_rready == 1'b1 && obi_rvalid == 1'b1;


  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_ph_cont <= 1'b0;
    end
    else begin
      if (obi_req == 1'b1 && obi_gnt == 1'b0) begin
        addr_ph_cont <= 1'b1;
      end
      else begin
        addr_ph_cont <= 1'b0;
      end
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      resp_ph_cont <= 1'b0;
    end
    else begin
      if (obi_rvalid == 1'b1 && obi_rready == 1'b0) begin
        resp_ph_cont <= 1'b1;
      end
      else begin
        resp_ph_cont <= 1'b0;
      end
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      v_addr_ph_cnt <= '0;
    end
    else begin
      if (addr_ph_valid && !rsp_ph_valid) begin
        v_addr_ph_cnt <= v_addr_ph_cnt + 1'b1;
      end
      else if (!addr_ph_valid && rsp_ph_valid && v_addr_ph_cnt > 0) begin
        v_addr_ph_cnt <= v_addr_ph_cnt - 1'b1;
      end
    end
  end

  assign  addr_ph_lapse_comb = addr_ph_valid ? 0 : addr_ph_lapse_ff;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_ph_lapse_ff <= 0;
    end else if (addr_ph_valid) begin
      addr_ph_lapse_ff <= 1;
    end else if (addr_ph_occured) begin
      addr_ph_lapse_ff <= addr_ph_lapse_ff + 1;
    end
  end

  always_latch  begin
    if (!rst_ni) begin
      addr_ph_occured = 0;
    end else if (addr_ph_valid) begin
      addr_ph_occured = 1;
    end
  end

  assign  addr_ph_occurances_comb = addr_ph_occurances_ff + addr_ph_valid;
  assign  rsp_ph_occurances_comb  = rsp_ph_occurances_ff  + rsp_ph_valid;
  assign  addr_ph_occurances = addr_ph_occurances_comb;
  assign  rsp_ph_occurances  = rsp_ph_occurances_comb;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_ph_occurances_ff <= 0;
      rsp_ph_occurances_ff  <= 0;
    end else begin
      if (addr_ph_valid) begin
        addr_ph_occurances_ff <= addr_ph_occurances_ff + 1;
      end

      if (rsp_ph_valid) begin
        rsp_ph_occurances_ff <= rsp_ph_occurances_ff + 1;
      end
    end
  end

  localparam int  MAX_OBI_STALLS = 8;
  property p_obi_max_stalls;
    obi_req && obi_gnt |-> !obi_rvalid [*0:MAX_OBI_STALLS] ##1 obi_rvalid;
  endproperty : p_obi_max_stalls
  asu_TODO: restrict property (p_obi_max_stalls);

endmodule : uvmt_cv32e40s_sl_obi_phases_monitor
