#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x, *y;
  x = malloc(sizeof(long)*2*L);
  for (size_t i = 0; i < 2*L; i++)
  {
    if (i < L)
    {
      x[i] = i;
    }
    else
    {
      if (i == L)
      {
        y = x;
      }
      y[i] = y[i-L];
    }
  }

  size_t i = nondet_int();
  if (i < L)
    assert(x[i] == x[i+L]);
  return 0;
}
