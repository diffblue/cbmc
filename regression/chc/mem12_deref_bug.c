#include <stdlib.h>
int nondet_int();

int main()
{
  size_t L = nondet_int();
  __CPROVER_assume(L > 0);
  long *x; // = malloc(sizeof(long)*2*L);
  for (size_t i = 0; i < 2*L; i = i + 2)
  {
    x[i] = i;
    x[i + 1] = x[i] + 1;
  }

  size_t i = nondet_int();
  // if (i < 2*L) assert(x[i] == i);
  return 0;
}
