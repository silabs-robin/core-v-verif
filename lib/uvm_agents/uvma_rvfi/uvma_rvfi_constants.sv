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


`ifndef __UVMA_RVFI_CONSTANTS_SV__
`define __UVMA_RVFI_CONSTANTS_SV__


// RVFI field widths
localparam ORDER_WL         = 64;
localparam MODE_WL          = 2;
localparam IXL_WL           = 2;
localparam TRAP_WL          = 14;
localparam GPR_ADDR_WL      = 5;
localparam RVFI_DBG_WL      = 3;
localparam RVFI_NMIP_WL     = 2;
localparam CYCLE_CNT_WL     = 32;
localparam NMEM             = 128;

// Fields within TRAP
localparam TRAP_EXCP_LSB         = 0;
localparam TRAP_EXCP_WL          = 1;
localparam TRAP_NONDBG_ENTRY_LSB = 1;
localparam TRAP_NONDBG_ENTRY_WL  = 1;
localparam TRAP_DBG_ENTRY_LSB    = 2;
localparam TRAP_DBG_ENTRY_WL     = 1;
localparam TRAP_CAUSE_LSB        = 3;
localparam TRAP_CAUSE_WL         = 6;
localparam TRAP_DBG_CAUSE_LSB    = 9;
localparam TRAP_DBG_CAUSE_WL     = 3;

// Lengths & Sizes
localparam DEFAULT_ILEN     = 32;
localparam DEFAULT_XLEN     = 32;
localparam DEFAULT_NRET     = 1;

// RISC-V Constants
parameter logic[ 2:0]  DBG_CAUSE_TRIGGER               =  3'h 2;
parameter logic[ 1:0]  PRIV_LVL_M                      =  2'b 11;
parameter logic[ 1:0]  PRIV_LVL_U                      =  2'b 00;
parameter logic[10:0]  EXC_CAUSE_INSTR_FAULT           = 11'h 1;
parameter logic[10:0]  EXC_CAUSE_LOAD_FAULT            = 11'h 5;
parameter logic[10:0]  EXC_CAUSE_STORE_FAULT           = 11'h 7;
parameter logic[10:0]  EXC_CAUSE_INSTR_INTEGRITY_FAULT = 11'h 19;
parameter logic[10:0]  EXC_CAUSE_INSTR_BUS_FAULT       = 11'h 18;

// Instr Matching - Loads
parameter logic[31:0]  INSTR_REF_LOAD       = 32'b 000000000000_00000000_00000000_0_0000011;
parameter logic[31:0]  INSTR_MASK_LOAD      = 32'b 000000000000_00000000_00000000_0_1111111;
parameter logic[31:0]  INSTR_REF_LW         = 32'b 000000000000_00000_010_00000_0000011;
parameter logic[31:0]  INSTR_MASK_LW        = 32'b 000000000000_00000_111_00000_1111111;
parameter logic[31:0]  INSTR_REF_CLWSP      = 32'b 00000000_00000000_010_0_00000_00000_10;
parameter logic[31:0]  INSTR_MASK_CLWSP     = 32'b 11111111_11111111_111_0_00000_00000_11;
parameter logic[31:0]  INSTR_REF_CLW        = 32'b 00000000_00000000_010_0_00000_00000_00;
parameter logic[31:0]  INSTR_MASK_CLW       = 32'b 11111111_11111111_111_0_00000_00000_11;
parameter logic[31:0]  INSTR_REF_CLBU       = 32'b 00000000_00000000_100_000_000_00_000_00;
parameter logic[31:0]  INSTR_MASK_CLBU      = 32'b 11111111_11111111_111_111_000_00_000_11;
parameter logic[31:0]  INSTR_REF_CLHU       = 32'b 00000000_00000000_100_001_000_0_0_000_00;
parameter logic[31:0]  INSTR_MASK_CLHU      = 32'b 11111111_11111111_111_111_000_1_0_000_11;
parameter logic[31:0]  INSTR_REF_CLH        = 32'b 00000000_00000000_100_001_000_1_0_000_00;
parameter logic[31:0]  INSTR_MASK_CLH       = 32'b 11111111_11111111_111_111_000_1_0_000_11;
parameter logic[31:0]  INSTR_REF_CMPOP      = 32'b 00000000_00000000_101_11010_0000_00_10;
parameter logic[31:0]  INSTR_MASK_CMPOP     = 32'b 11111111_11111111_111_11111_0000_00_11;
parameter logic[31:0]  INSTR_REF_CMPOPRET   = 32'b 00000000_00000000_101_11110_0000_00_10;
parameter logic[31:0]  INSTR_MASK_CMPOPRET  = 32'b 11111111_11111111_111_11111_0000_00_11;
parameter logic[31:0]  INSTR_REF_CMPOPRETZ  = 32'b 00000000_00000000_101_11100_0000_00_10;
parameter logic[31:0]  INSTR_MASK_CMPOPRETZ = 32'b 11111111_11111111_111_11111_0000_00_11;

// Instr Matching - Stores
parameter logic[31:0]  INSTR_REF_STORE  = 32'b 00000000_00000000_00000000_0_0100011;
parameter logic[31:0]  INSTR_MASK_STORE = 32'b 00000000_00000000_00000000_0_1111111;
parameter logic[31:0]  INSTR_REF_CSWSP  = 32'b 00000000_00000000_110_000000_00000_10;
parameter logic[31:0]  INSTR_MASK_CSWSP = 32'b 11111111_11111111_111_000000_00000_11;
parameter logic[31:0]  INSTR_REF_CSW    = 32'b 00000000_00000000_110_000_000_00_000_00;
parameter logic[31:0]  INSTR_MASK_CSW   = 32'b 11111111_11111111_111_000_000_00_000_11;
parameter logic[31:0]  INSTR_REF_CSB    = 32'b 00000000_00000000_100_010_000_00_000_00;
parameter logic[31:0]  INSTR_MASK_CSB   = 32'b 11111111_11111111_111_111_000_00_000_11;
parameter logic[31:0]  INSTR_REF_CSH    = 32'b 00000000_00000000_100_011_000_0_0_000_00;
parameter logic[31:0]  INSTR_MASK_CSH   = 32'b 11111111_11111111_111_111_000_1_0_000_11;
parameter logic[31:0]  INSTR_REF_PUSH   = 32'b 00000000_00000000_101_11000_0000_00_10;
parameter logic[31:0]  INSTR_MASK_PUSH  = 32'b 11111111_11111111_111_11111_0000_00_11;


`endif // __UVMA_RVFI_CONSTANTS_SV__
