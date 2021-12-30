#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  size_t j = nondet_int();
  __CPROVER_assume (L > 10 && i < L && j < L);
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  x[i] = i;
  y[j] = j;
  long *z;
  if (i > j)
  {
    z = x;
    z[j] = y[j];
  }
  else
  {
    z = y;
    z[i] = x[i];
  }
  assert(z[i] + z[j] == i + j);
  free(x);
  free(y);
  return 0;
}
