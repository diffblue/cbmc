#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  long *z;
  for (size_t i = 0; i < L; i++)
  {
    z = x;
    z[i] = 0;
    z = y;
    z[i] = 1;
  }

  size_t i = nondet_int();
  if (i < L)
    assert(x[i] + y[i] == 1);
  return 0;
}
