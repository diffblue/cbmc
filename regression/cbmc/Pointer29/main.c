#include <assert.h>

int main()
{
  unsigned int *s_pdt = (unsigned int *)(0xdeadbeef);
  // this is well defined
  assert((unsigned long long)s_pdt > 1);
  // this is undefined as it could both be a comparison over integers as well as
  // over pointers; the latter may mean comparing pointers to different objects,
  // so guard against that
  assert(
    __CPROVER_POINTER_OBJECT(s_pdt) !=
      __CPROVER_POINTER_OBJECT((unsigned int *)1) ||
    s_pdt > 1);
  return 0;
}
