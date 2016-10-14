#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;

  if ((__CPROVER_string_equal(x, __CPROVER_string_literal("f")) || __CPROVER_string_equal(x, __CPROVER_string_literal("abcd")))
      && ((unsigned)__CPROVER_string_length(x)) > ((unsigned)3)
      && ((unsigned)__CPROVER_string_length(x)) < ((unsigned)5)) {
    assert(0);
  }
  return 0;
}
