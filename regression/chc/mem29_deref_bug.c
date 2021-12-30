#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t M = nondet_int();
  long *x, *y, *z, *w;
  x = malloc(sizeof(long)*L);
  y = malloc(sizeof(long)*M);
  __CPROVER_assume(L > 0 && M > 0);
  z = x;
  // w = y;
  for (size_t i = 0; i < L || i < M; i++)
  {
    if(i < L && i < M)
    {
      z[i] = 0;
      w[i] = 1;
    }
    else
    {
      if (i < L)
      {
        w = x;
        w[i] = 0;
      }
      else
      {
        z = y;
        z[i] = 1;
      }
    }
  }

  size_t i = nondet_int();
  // if (i < L)
  //   assert(x[i] == 0);
  // if (i < M)
  //   assert(y[i] == 1);
  return 0;
}
