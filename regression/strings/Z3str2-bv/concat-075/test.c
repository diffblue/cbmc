#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string m2;
  __CPROVER_string x1;
  __CPROVER_string x2;
  __CPROVER_string x3;
  __CPROVER_string y2;

  if (__CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_literal("ef"), y2), __CPROVER_string_concat(x1, x2))
      && __CPROVER_string_equal(__CPROVER_string_concat(x3, __CPROVER_string_concat(__CPROVER_string_literal("ce"), m2)), __CPROVER_string_concat(__CPROVER_string_literal("ef"), y2))) {
    assert(0);
  }
  return 0;
}
