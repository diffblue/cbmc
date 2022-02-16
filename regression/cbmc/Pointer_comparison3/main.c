#include <assert.h>
#include <stdlib.h>

char *nondet_pointer();

int main()
{
  int *p1 = malloc(sizeof(int));

  assert(p1 < p1 + 1);

  int *p2 = malloc(sizeof(int));

  assert(p1 != p2);

  _Bool nondet;
  // In the current implementation, CBMC always produces "false" for a
  // comparison over different objects. This could change at any time, which
  // would require updating this test.
  if(nondet)
    __CPROVER_assert(p1 < p2, "always false for different objects");
  else
    __CPROVER_assert(p1 > p2, "always false for different objects");

  char *p = nondet_pointer();

  __CPROVER_assume(p < p1 + 1);
  assert(__CPROVER_POINTER_OBJECT(p) == __CPROVER_POINTER_OBJECT(p1));
}
