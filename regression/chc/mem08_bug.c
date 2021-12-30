#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  size_t j = nondet_int();

  __CPROVER_assume (L > 10 && i < L && j < L);
  long *x, *y;
  int tmp;
  if (nondet_int())
  {
    x = malloc(sizeof(long)*L);
    tmp = 1;
  }
  else
  {
    y = malloc(sizeof(long)*L);
    tmp = 0;
  }
  if (tmp)
  {
    x[i] = nondet_int();
    if (x[i] < 0) x[i] = -x[i];
  }
  else
  {
    y[i] = nondet_int();
    if (y[i] > 0) y[i] = -y[i];
  }
  if (nondet_int())
  {
    y = x;
  }
  else
  {
    x = y;
  }

  if (tmp)
  {
    assert(x[i] >= 0);
  }
  else
  {
    assert(x[i] <= 0);
  }
  free(x);
  return 0;
}
