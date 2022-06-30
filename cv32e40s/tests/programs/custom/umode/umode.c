// TODO:ropeders license header


#include <stdio.h>
#include <stdlib.h>


extern volatile int  myfunc(void);
extern volatile void run_in_umode(int (*funptr)(void));


int main(void) {
  int x;

  // Easily visible header
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("nop");

  x = myfunc();
  printf("x = %d\n", x);

  run_in_umode(myfunc);

  // Easily visible footer
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  return EXIT_SUCCESS;
}
