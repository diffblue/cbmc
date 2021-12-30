#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  size_t j = nondet_int();
  __CPROVER_assume (L > 10 && i < L && j < L);
  long *x = malloc(sizeof(long)*L);
  x[i] = 1;
  long *y = x;
  y[j] = 2;
  assert(y[i] < y[j]);
  free(x);
  return 0;
}
