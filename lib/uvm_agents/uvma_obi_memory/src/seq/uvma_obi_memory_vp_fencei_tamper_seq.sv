// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.


`ifndef __UVMA_OBI_MEMORY_VP_FENCEI_TAMPER_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_FENCEI_TAMPER_SEQ_SV__


class uvma_obi_memory_vp_fencei_tamper_seq_c extends uvma_obi_memory_vp_base_seq_c;

  `uvm_object_utils(uvma_obi_memory_vp_fencei_tamper_seq_c)

  extern function new(string name="uvma_obi_memory_vp_fencei_tamper_seq_c");
  extern virtual task body();
  extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);
  extern virtual function int unsigned get_num_words();

endclass : uvma_obi_memory_vp_fencei_tamper_seq_c


function uvma_obi_memory_vp_fencei_tamper_seq_c::new(string name="uvma_obi_memory_vp_fencei_tamper_seq_c");

  super.new(name);

endfunction : new


task uvma_obi_memory_vp_fencei_tamper_seq_c::body();

  $display("TODO body");

endtask : body


task uvma_obi_memory_vp_fencei_tamper_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

endtask : vp_body


function int unsigned uvma_obi_memory_vp_fencei_tamper_seq_c::get_num_words();

   return 1;

endfunction : get_num_words


`endif // __UVMA_OBI_MEMORY_VP_FENCEI_TAMPER_SEQ_SV__
