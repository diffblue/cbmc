#include <stdlib.h>

int main()
{
  size_t n;
  int *p = (int *)malloc(n);
  int *q = (int *)malloc(n);
  __CPROVER_assert(p, "not-null");
  __CPROVER_assert(q, "not-null");
  return 0;
}
