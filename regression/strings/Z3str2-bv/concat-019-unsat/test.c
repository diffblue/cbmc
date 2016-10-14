#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string a;

  if (__CPROVER_string_equal(__CPROVER_string_concat(a, __CPROVER_string_literal("testhello")), __CPROVER_string_literal("test"))) {
    assert(0);
  }
  return 0;
}
