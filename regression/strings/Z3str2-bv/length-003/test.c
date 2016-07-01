#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(y, __CPROVER_string_literal("abcde"))
      && __CPROVER_string_equal(y, x)
      && ((unsigned)__CPROVER_string_length(x)) <= ((unsigned)5)) {
    assert(0);
  }
  return 0;
}
