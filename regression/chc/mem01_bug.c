#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  if (L > 1 && i + 1 < L)
  {
    long *x = malloc(sizeof(long)*L);
    x[i] = 53;
    long *y = x;
    y[i+1] = y[i] - 8;
    assert(x[i+1] > x[i]);
    free(x);
  }
  return 0;
}
