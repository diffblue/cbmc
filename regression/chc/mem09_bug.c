#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  size_t i = nondet_int();
  size_t j = nondet_int();

  __CPROVER_assume (L > 10 && i < L && j < L);
  long *x, *y, *z, *w;
  x = malloc(sizeof(long)*L);
  y = malloc(sizeof(long)*L);
  x[i] = nondet_int();
  y[j] = nondet_int();
  if (x[i] == y[j])
  {
    x[j] = nondet_int();
    y[i] = x[j];
    z = x;
    w = y;
    long t1 = z[i] + w[i];
    long t2 = z[j] + w[i];
    assert(t1 == t2);
    x[0] = t1;
    y[0] = t2;
    assert(x[0] == y[0]);
  }
  free(x);
  free(y);
  return 0;
}
