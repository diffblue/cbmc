#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  size_t i;
  long res = 0;
  for (i = 0; i < L; i++)
  {
    if (res > 10) break;
    if (x[i] < 0) break;
    if (x[i] > 1) break;
    res = res + x[i];
    y[i] = res;
  }

  size_t j = nondet_int();
  if (j + 1 < i && j < L)
    assert(y[j+1] >= y[j]);
  return 0;
}
