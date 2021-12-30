#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  if (L > 0 && i < L)
  {
    long *x;
    x[i] = 371;
    long *y = x;
    y[i] = y[i] + 5;
    //assert(x[i] == 376);
    free(x);
  }
  return 0;
}
