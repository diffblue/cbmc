#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  __CPROVER_assume(L > 0);
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
    y = x;
  else
    x = y;

  for (size_t i = 0; i < L; i++)
  {
    if (nondet_int())
      x[i] = i;
    else
      y[i] = i;
  }

  size_t i = nondet_int();
  if (i < L) assert(x[i] == i);
  if (tmp)
    free(x);
  else
    free(y);

  return 0;
}
