#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x, *y, *z;
  x = malloc(sizeof(long)*L);
  y = malloc(sizeof(long)*L);
  __CPROVER_assume(L > 0);
  int tmp;
  if (nondet_int())
  {
    tmp = 1;
    z = x;
  }
  else
  {
    tmp = 0;
    // z = y;
  }
  for (size_t i = 0; i < L; i++)
  {
    z[i] = i;
  }

  if (tmp)
  {
    z = y;
  }
  else
  {
    z = x;
  }

  for (size_t i = 0; i < L; i++)
  {
    z[i] = i;
  }

  size_t i = nondet_int();
  // if (i < L)
  //   assert(x[i] == y[i]);
  return 0;
}
