#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  __CPROVER_assume (L > 10 && i < L);
  long *x, *y, *z;

  x = malloc(sizeof(long)*L);
  x[i] = 5;
  z = x;
  y = malloc(sizeof(long)*L);
  y[i] = 8;
  z = y;

  assert(z[i] == 5);
  free(x);
  free(y);
  return 0;
}
