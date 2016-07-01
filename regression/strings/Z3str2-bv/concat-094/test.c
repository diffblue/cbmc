#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y1;
  __CPROVER_string y2;

  if (__CPROVER_string_equal(x, __CPROVER_string_literal("abc
efg  "))
      && __CPROVER_string_equal(y1, __CPROVER_string_literal("zzz"))) {
    assert(0);
  }
  return 0;
}
