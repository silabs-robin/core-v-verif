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


module uvmt_cv32e40x_exceptions_assert (
  uvmt_cv32e40x_exceptions_if  eif
);

  //TODO assign eif.is_ibus_breakpoint_addr = ???;
  //TODO assign eif.is_ibus_pma = ???;
  assign eif.is_ibus_buserr = eif.wb_valid && eif.err;
  assign eif.is_instr_illegal = eif.wb_valid && eif.illegal_insn;
  assign eif.is_instr_ecall = eif.wb_valid && (eif.rdata == 32'h 00000073);
  assign eif.is_instr_ebreak = eif.wb_valid && (eif.rdata inside {32'h 00100073, 32'h 9002});
  //TODO assign eif.is_dbus_breakpoint_addr = ???;
  //TODO assign eif.is_dbus_breakpoint_data = ???;
  //TODO assign eif.is_dbus_pma_store_misaligned = ???;
  //TODO assign eif.is_dbus_pma_store_amo = ???;
  //TODO assign eif.is_dbus_pma_store_conditional = ???;
  //TODO assign eif.is_dbus_pma_load_misaligned = ???;
  //TODO assign eif.is_dbus_pma_load_reserved = ???;

endmodule : uvmt_cv32e40x_exceptions_assert
