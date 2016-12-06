#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s1,s2;
  __CPROVER_string t = __CPROVER_string_concat(s1, s2);
  __CPROVER_assume(__CPROVER_string_isprefix(__CPROVER_string_literal("a1"),s1));

  __CPROVER_assume(__CPROVER_string_contains(s2,__CPROVER_string_literal("12")));

  __CPROVER_assume(__CPROVER_string_issuffix(__CPROVER_string_literal("cd"),t));

  assert(__CPROVER_string_length(t) > 3);
  assert(__CPROVER_string_length(t) > 4);
  return 0;
}
