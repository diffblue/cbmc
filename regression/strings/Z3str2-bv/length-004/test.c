#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(y, x)
      && (__CPROVER_string_length(y) == 4)
      && (__CPROVER_string_equal(x, __CPROVER_string_literal("fg")) || __CPROVER_string_equal(x, __CPROVER_string_literal("abcd")))) {
    assert(0);
  }
  return 0;
}
