#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x1;
  __CPROVER_string x2;
  __CPROVER_string y1;
  __CPROVER_string y2;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x1, x2), __CPROVER_string_literal("testhello"))
      && (__CPROVER_string_length(x1) == 1)
      && __CPROVER_string_equal(__CPROVER_string_concat(y1, y2), __CPROVER_string_literal("testhello"))
      && (__CPROVER_string_length(y2) == 5)) {
    assert(0);
  }
  return 0;
}
