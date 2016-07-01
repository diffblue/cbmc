#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, __CPROVER_string_literal("b")), __CPROVER_string_concat(__CPROVER_string_literal("a"), x))) {
    assert(0);
  }
  return 0;
}
