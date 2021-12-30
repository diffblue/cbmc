#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  __CPROVER_assume(L > 0);
  long *x = malloc(sizeof(long)*L);
  x[0] = 0;
  for (size_t i = 1; i < L; i++)
  {
    x[i] = x[i - 1];
  }

  size_t i = nondet_int();
  if (i < L) assert(x[i] == 0);
  return 0;
}
