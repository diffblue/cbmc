#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string m2;
  __CPROVER_string t_str2;
  __CPROVER_string t_str5;
  __CPROVER_string y2;
  __CPROVER_string z;

  if (__CPROVER_string_equal(z, __CPROVER_string_concat(__CPROVER_string_literal("ef"), y2))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(t_str5, __CPROVER_string_concat(__CPROVER_string_literal("ce"), m2)))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(t_str2, __CPROVER_string_literal("abc@")))) {
    assert(0);
  }
  return 0;
}
