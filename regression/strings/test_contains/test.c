#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s1 = __CPROVER_string_literal("a1");
  __CPROVER_string s2 = __CPROVER_string_literal("2b");
  __CPROVER_string t = __CPROVER_string_concat(s1, s2);
  
  assert(!__CPROVER_string_contains(t,__CPROVER_string_literal("3")));
  assert(__CPROVER_string_contains(t,__CPROVER_string_literal("12")));
  assert(!__CPROVER_string_contains(t,__CPROVER_string_literal("b")));
  return 0;
}
