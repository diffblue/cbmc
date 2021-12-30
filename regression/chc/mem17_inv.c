#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  long *x = malloc(sizeof(long)*L);
  long *y = malloc(sizeof(long)*L);
  for (size_t i = 0; i < L; i++)
  {
    long t1 = (x[i] > y[i] ? x[i] : y[i]);
    long t2 = (x[i] < y[i] ? x[i] : y[i]);
    x[i] = t1;
    y[i] = t2;
  }

  size_t i = nondet_int();
  if (i < L)
    assert(x[i] >= y[i]);
  return 0;
}
