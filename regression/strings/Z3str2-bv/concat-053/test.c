#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_literal("abcefgh"), x), __CPROVER_string_concat(__CPROVER_string_literal("abc"), y))
      && (__CPROVER_string_length(x) == 1)) {
    assert(0);
  }
  return 0;
}
