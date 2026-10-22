#include <stdlib.h>
// A path symbolic execution has not ruled out reads a size_t 8 bytes before
// a dynamically allocated array of symbolic size: a byte_extract with a
// negative constant offset, which lowering must not reject.  The bytes
// before the object are unconstrained.
int main()
{
  __CPROVER_size_t n;
  __CPROVER_assume(n > 0 && n < 4);
  unsigned short *a = malloc(n * sizeof(unsigned short));
  if(!a)
    return 0;
  a[0] = 7;
  __CPROVER_size_t *p = (__CPROVER_size_t *)((char *)a - 8);
  int k;
  if(k)
    __CPROVER_assert(*p == 0, "read before the object");
  __CPROVER_assert(a[0] == 7, "in bounds");
  __CPROVER_assert(a[0] == 8, "WRONG (must FAIL)");
  return 0;
}
