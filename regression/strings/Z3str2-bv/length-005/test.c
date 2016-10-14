#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(__CPROVER_string_literal("abcd"), __CPROVER_string_concat(x, y))
      && ((unsigned)__CPROVER_string_length(y)) >= ((unsigned)3)
      && ((unsigned)__CPROVER_string_length(x)) >= ((unsigned)1)) {
    assert(0);
  }
  return 0;
}
