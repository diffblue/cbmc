#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string v1;
  __CPROVER_string v2;
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_concat(v1, v2), __CPROVER_string_literal("e")), __CPROVER_string_concat(x, y))) {
    assert(0);
  }
  return 0;
}
