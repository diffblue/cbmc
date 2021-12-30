#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  __CPROVER_assume(L > 5);
  long *x, *y;
  for (size_t i = 0; i < L; i++)
  {
    if (i < 5) {}
    else
    {
      if (i == 5)
      {
        x = malloc(sizeof(long)*L);
      }
      else
      {
        y = x;
      }
      x[i] = i;
    }
  }

  size_t i = nondet_int();
  if (5 < i && i < L)
    assert(y[i] == i);
  return 0;
}
