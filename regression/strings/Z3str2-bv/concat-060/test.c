#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, __CPROVER_string_literal("ab")), __CPROVER_string_concat(y, __CPROVER_string_literal("iab")))) {
    assert(0);
  }
  return 0;
}
