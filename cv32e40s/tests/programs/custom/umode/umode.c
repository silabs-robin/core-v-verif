// TODO:ropeders license header


#include <stdio.h>
#include <stdlib.h>


extern volatile int myfunc(void);


int main(void) {
  int x;

  printf("\nTODO umode\n\n");

  x = myfunc();
  printf("x = %d\n", x);

  return EXIT_SUCCESS;
}
