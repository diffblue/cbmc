#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x, *y, *z;
  x = malloc(sizeof(long)*L);
  __CPROVER_assume(L > 0);
  y = x;
  for (size_t i = 0; i < L; i++)
  {
    y[i] = 0;
  }
  z = malloc(sizeof(long)*L);
  for (size_t i = 0; i < L; i++)
  {
    z[i]++;
  }

  size_t i = nondet_int();
  if (i < L)
    assert(x[i] == 1);
  return 0;
}
