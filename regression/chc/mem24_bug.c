#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  long *z;
  long *w;
  for (size_t i = 0; i < L; i++)
  {
    if (i % 2 == 0)
    {
      z = x;
      w = y;
    }
    else
    {
      z = x;
      w = x;
    }
    long m = (z[i] > w[i] ? z[i] : w[i]);
    x[i] = m;
  }

  size_t i = nondet_int();
  if (i < L)
    assert(x[i] >= y[i]);
  return 0;
}
