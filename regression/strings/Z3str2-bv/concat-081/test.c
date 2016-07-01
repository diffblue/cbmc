#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string m1;
  __CPROVER_string m2;
  __CPROVER_string x1;
  __CPROVER_string x2;
  __CPROVER_string y1;
  __CPROVER_string y2;
  __CPROVER_string z;

  if (__CPROVER_string_equal(z, __CPROVER_string_concat(x1, __CPROVER_string_concat(__CPROVER_string_literal("abc"), x2)))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(y1, __CPROVER_string_concat(__CPROVER_string_literal("ef"), y2)))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(m1, __CPROVER_string_concat(__CPROVER_string_literal("ce"), m2)))
      && (__CPROVER_string_length(z) == 9)) {
    assert(0);
  }
  return 0;
}
