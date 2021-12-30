#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  __CPROVER_assume(L > 0);
  long *x = malloc(sizeof(long)*L);
  long m = x[0];
  for (size_t i = 1; i < L; i++)
  {
    if (m > x[i])
      m = x[i];
  }

  size_t i = nondet_int();
  if (i < L) assert(m <= x[i]);
  return 0;
}
