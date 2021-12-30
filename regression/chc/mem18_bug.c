#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  size_t i;
  for (i = 0; i < L; i++)
  {
    if (x[i] < 0) break;
    y[i] = x[i];
  }

  size_t j = nondet_int();
  if (j < L)
    assert(y[j] >= 0);
  return 0;
}
