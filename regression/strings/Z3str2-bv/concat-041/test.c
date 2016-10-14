#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, y), __CPROVER_string_concat(z, __CPROVER_string_literal("abc")))
      && (__CPROVER_string_length(y) == 1)
      && (__CPROVER_string_length(x) == 3)) {
    assert(0);
  }
  return 0;
}
