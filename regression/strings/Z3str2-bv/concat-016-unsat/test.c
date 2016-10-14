#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string a;

  if (__CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_literal("tesk"), a), __CPROVER_string_literal("testhello"))) {
    assert(0);
  }
  return 0;
}
