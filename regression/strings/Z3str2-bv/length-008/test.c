#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x1;
  __CPROVER_string x2;
  __CPROVER_string x3;
  __CPROVER_string y;

  if (__CPROVER_string_equal(y, __CPROVER_string_concat(x1, __CPROVER_string_concat(x2, x3)))
      && __CPROVER_string_equal(x2, __CPROVER_string_literal("abc"))
      && (__CPROVER_string_length(x1) == 1)
      && (__CPROVER_string_length(y) == 4)) {
    assert(0);
  }
  return 0;
}
