#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x1;
  __CPROVER_string x2;
  __CPROVER_string y2;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x1, __CPROVER_string_concat(__CPROVER_string_literal("ef"), y2)), __CPROVER_string_concat(__CPROVER_string_literal("abc"), x2))
      && (__CPROVER_string_length(x1) == 4)) {
    assert(0);
  }
  return 0;
}
