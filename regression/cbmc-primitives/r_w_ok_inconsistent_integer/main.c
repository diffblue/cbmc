#include <assert.h>
#include <stdlib.h>

void main()
{
  // pointer with object bits = 123 and offset = 123
  // this is to test with a pointer that does not point to valid memory, but the
  // value of which is otherwise not special in any way (like for example a null
  // pointer)
  char *p = (size_t)123 << (sizeof(char *) * 8 - 8) | 123;
  __CPROVER_assume(__CPROVER_r_ok(p, 10));
  assert(0); // fails
  *p;        // succeeds
}
