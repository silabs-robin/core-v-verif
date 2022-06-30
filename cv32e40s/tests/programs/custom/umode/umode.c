// TODO:ropeders license header


#include <stdio.h>
#include <stdlib.h>


extern volatile int  myfunc(void);
//extern volatile void run_in_umode(int (*funptr)(void));
extern volatile int  run_in_umode(int (*funptr)(void));
extern volatile void setup_pmp(void);
extern volatile void set_mmode(void);


void u_sw_irq_handler(void) {
  uint32_t mcause;

  printf("u_sw_irq_handler\n");

  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(mcause));
  printf("mcause = %d\n", mcause);

  exit(EXIT_FAILURE);
}


int main(void) {
  int x;

  // Easily visible header
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("nop");

  x = 0;
  printf("x = %d\n", x);
  x = myfunc();
  printf("x = %d\n", x);

  setup_pmp();

  x = 0;
  printf("x = %d\n", x);
  x = run_in_umode(myfunc);
  set_mmode();
  printf("x = %d\n", x);

  // Easily visible footer
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  return EXIT_SUCCESS;
}
