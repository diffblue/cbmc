#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t M = nondet_int();
  long *x, *y, *z;
  x = malloc(sizeof(long)*L);
  y = malloc(sizeof(long)*M);
  __CPROVER_assume(L > 0 && M > 0 && L < 100 && M < 100);
  for (size_t i = 0; i < L+M; i++)
  {
    long j;
    if (i < L)
    {
      // z = x;
      j = 0;
    }
    else
    {
      z = y;
      j = L;
    }
    z[i-j] = i-j;
  }

  size_t i = nondet_int();
  // if (i < L && i < M)
  //   assert(x[i] == y[i]);
  return 0;
}
