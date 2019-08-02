#include <stdlib.h>

int main()
{
  size_t n;
  int *p = (int *)malloc(n);
  int *q = (int *)malloc(n);
  __CPROVER_assert(p, "not-null");
  __CPROVER_assert(q, "not-null");
  // the following is the same as assuming false
  __CPROVER_assume(__CPROVER_POINTER_OBJECT(p) == __CPROVER_POINTER_OBJECT(q));
  return 0;
}
