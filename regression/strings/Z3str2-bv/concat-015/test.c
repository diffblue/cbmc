#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string a;
  __CPROVER_string b;

  if ((__CPROVER_string_equal(__CPROVER_string_concat(a, b), __CPROVER_string_literal("te")) || __CPROVER_string_equal(__CPROVER_string_concat(b, a), __CPROVER_string_literal("te")))
      && __CPROVER_string_equal(b, __CPROVER_string_literal("t"))) {
    assert(0);
  }
  return 0;
}
