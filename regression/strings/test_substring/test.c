#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s = __CPROVER_string_literal("abcdef");
  __CPROVER_string t = __CPROVER_string_substring(s,2,4);

  assert(__CPROVER_string_equal(t,__CPROVER_string_literal("cd")));
  assert(__CPROVER_string_equal(t,__CPROVER_string_literal("cc")));
  assert(!__CPROVER_string_equal(t,__CPROVER_string_literal("bc")));
  assert(!__CPROVER_string_equal(t,__CPROVER_string_literal("cd")));
  return 0;
}
