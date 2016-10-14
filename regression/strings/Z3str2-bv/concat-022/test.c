#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, y), z)
      && (__CPROVER_string_equal(z, __CPROVER_string_literal("abcdef")) || __CPROVER_string_equal(z, __CPROVER_string_literal("aaaa")) || __CPROVER_string_equal(z, __CPROVER_string_literal("bbbb")))
      && (__CPROVER_string_equal(x, __CPROVER_string_literal("e")) || __CPROVER_string_equal(x, __CPROVER_string_literal("f")) || __CPROVER_string_equal(x, __CPROVER_string_literal("abcde")))) {
    assert(0);
  }
  return 0;
}
