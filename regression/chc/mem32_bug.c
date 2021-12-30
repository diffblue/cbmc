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
    y[i] = 1;
  }

  z = y;
  for (size_t i = 0; i < L; i++)
  {
    z[i] = 2;
  }
  y = malloc(sizeof(long)*L);
  for (size_t i = 0; i < L; i++)
  {
    y[i]++;
  }
  size_t i = nondet_int();
  if (i < L)
    assert(x[i] == y[i]);
  return 0;
}
