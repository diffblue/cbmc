#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string Y3;
  __CPROVER_string Y4;
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, __CPROVER_string_literal("abc")), __CPROVER_string_concat(__CPROVER_string_literal("ef"), y))
      && __CPROVER_string_equal(__CPROVER_string_concat(y, Y3), __CPROVER_string_concat(Y4, x))) {
    assert(0);
  }
  return 0;
}
