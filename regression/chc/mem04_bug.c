#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  __CPROVER_assume (L > 10 && i < L);
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  x[i] = 0;
  y[i] = 1;
  long *z;
  if (nondet_int())
  {
    z = x;
  }
  else
  {
    z = y;
  }
  z[i]++;
  assert(z[i] == 1);
  free(x);
  free(y);
  return 0;
}
