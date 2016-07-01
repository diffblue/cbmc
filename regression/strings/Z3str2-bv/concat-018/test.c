#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, y), __CPROVER_string_literal("testHello"))
      && __CPROVER_string_equal(__CPROVER_string_concat(y, z), __CPROVER_string_literal("low"))
      && !(__CPROVER_string_equal(y, __CPROVER_string_literal("")))) {
    assert(0);
  }
  return 0;
}
