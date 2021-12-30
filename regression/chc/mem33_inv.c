#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x, *y, *z;
  x = malloc(sizeof(long)*L);
  y = malloc(sizeof(long)*L);
  __CPROVER_assume(L > 0);
  size_t i;
  z = x;
  for (i = 0; i < L; i++)
  {
    if (z[i] >= 10)
    {
      z = y;
      for (size_t j = 0; j < i; j++)
      {
        z[j] = x[i];
      }
      break;
    }
  }
  size_t j = nondet_int();
  if (j < i && i < L)
    assert(y[j] > x[j]);
  return 0;
}
