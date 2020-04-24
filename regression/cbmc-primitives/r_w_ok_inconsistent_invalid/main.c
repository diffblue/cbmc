#include <assert.h>
#include <stdlib.h>

void main()
{
  // special value of the invalid pointer (object bits = 1 and offset = 0), as
  // checked for by __CPROVER_is_invalid_pointer()
  char *p = (size_t)1 << (sizeof(char *) * 8 - 8);
  __CPROVER_assume(__CPROVER_r_ok(p, 10));
  assert(0); // fails
  *p;        // succeeds
}
