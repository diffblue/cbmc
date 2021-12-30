#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  size_t tmp;
  __CPROVER_assume (L > 10 && i < L);
  long *x, *y, *z;

  if (nondet_int())
  {
    x = malloc(sizeof(long)*L);
    x[i] = 5;
    z = x;
    tmp = 1;
  }
  else
  {
    // y = malloc(sizeof(long)*L);
    y[i] = 8;
    z = y;
    tmp = 0;
  }
  //assert(z[i] >= 5);
  if (tmp)
    free(x);
  else
    free(y);
  return 0;
}
