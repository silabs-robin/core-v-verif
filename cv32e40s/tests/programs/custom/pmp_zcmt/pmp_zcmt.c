// Copyright 2023 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you
// may not use this file except in compliance with the License, or, at your
// option, the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdio.h>
#include <stdlib.h>

void
todo_my_test(void) {
  printf("TODO my test\n");
  exit(EXIT_SUCCESS);
}

__attribute__(( naked, aligned(64) ))
void
jvt_table(void) {
  __asm__ volatile(
    R"(
      todo_my_test
    )"
  );
}

static void
set_jvt(void) {
  __asm__ volatile(
    "csrw  jvt,  %[jvt_table]"
    : : [jvt_table] "r" (jvt_table)
  );
}

int
main(void) {
  printf("running 'pmp_zcmt' test\n");

  set_jvt();
  __asm__ volatile("cm.jt 0");

  return EXIT_SUCCESS;
}
