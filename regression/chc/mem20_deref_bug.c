#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  __CPROVER_assume(L > 0);
  long *x = malloc(sizeof(long)*L);
  long *y; //= x;
  for (size_t i = 0; i < L; i++)
  {
    if (nondet_int())
      x[i] = i;
    else
      y[i] = i;
  }

  size_t i = nondet_int();
  // if (i < L) assert(x[i] == i);
  free(x);
  return 0;
}
