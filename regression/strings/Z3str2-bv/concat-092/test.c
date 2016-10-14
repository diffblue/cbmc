#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x1;
  __CPROVER_string x2;
  __CPROVER_string y;

  if (__CPROVER_string_equal(y, __CPROVER_string_concat(__CPROVER_string_concat(x1, __CPROVER_string_literal("b")), __CPROVER_string_concat(__CPROVER_string_literal("a"), x2)))) {
    assert(0);
  }
  return 0;
}
