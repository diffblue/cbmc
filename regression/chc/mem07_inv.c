#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  size_t j = nondet_int();

  __CPROVER_assume (L > 10 && i < L && j < L);
  long *x, *y;
  x = malloc(sizeof(long)*L);
  x[i] = nondet_int();
  y = x;
  long val = y[i];
  if (val < 0) val = -val;
  x[j] = val;

  assert(y[i] <= y[j]);
  free(x);
  return 0;
}
