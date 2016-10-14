#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string a;
  __CPROVER_string b;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(a, b), __CPROVER_string_literal("testhello"))
      && __CPROVER_string_equal(a, __CPROVER_string_literal("testhe"))) {
    assert(0);
  }
  return 0;
}
