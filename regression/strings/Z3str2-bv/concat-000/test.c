#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string a;
  __CPROVER_string b;
  __CPROVER_string c1;
  __CPROVER_string c2;
  __CPROVER_string x;

  if (__CPROVER_string_equal(a, __CPROVER_string_concat(__CPROVER_string_concat(__CPROVER_string_literal("te"), c1), __CPROVER_string_concat(__CPROVER_string_literal("	"), c2)))
      && __CPROVER_string_equal(a, b)
      && __CPROVER_string_equal(x, __CPROVER_string_literal("str  "))) {
    assert(0);
  }
  return 0;
}
