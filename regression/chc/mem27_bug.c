#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x, *y, *z;
  x = malloc(sizeof(long)*L);
  y = malloc(sizeof(long)*L);
  size_t i;
  for (i = 0; i < L; i++)
  {
    if (x[i] != y[i]) break;
    if (nondet_int())
    {
      z = x;
    }
    else
    {
      z = y;
    }
    z[i]++;
  }

  size_t j = nondet_int();
  if (j < L)
    assert(x[j] != y[j]);
  return 0;
}
