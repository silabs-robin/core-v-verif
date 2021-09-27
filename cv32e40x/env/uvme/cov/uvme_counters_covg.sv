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


class uvme_counters_covg extends uvm_component;

  uvme_cv32e40x_cntxt_c cntxt;

  `uvm_component_utils(uvme_counters_covg);

  extern function new(string name = "counters_covg", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  covergroup cg_mcountinhibit;
    `per_instance_fcov
    cp_TODO: coverpoint cntxt.counters_vif.mon_cb.mcountinhibit;
  endgroup : cg_mcountinhibit

endclass : uvme_counters_covg


function uvme_counters_covg::new(string name = "counters_covg", uvm_component parent = null);

  super.new(name, parent);

  cg_mcountinhibit = new();

endfunction : new


function void uvme_counters_covg::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvme_cv32e40x_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (cntxt == null) `uvm_fatal("COUNTERSCOVG", "No cntxt object passed to model");

endfunction : build_phase


task uvme_counters_covg::run_phase(uvm_phase phase);

  super.run_phase(phase);

  while (1) begin
    @(cntxt.counters_vif.mon_cb);

    cg_mcountinhibit.sample();
  end

endtask : run_phase
