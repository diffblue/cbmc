#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string t;
  __CPROVER_string s = __CPROVER_string_concat(t, t);
  __CPROVER_assume(__CPROVER_string_equal(s, __CPROVER_string_literal("aa")));
 
  assert(t  == __CPROVER_string_literal("a"));
  assert(t  != __CPROVER_string_literal("a"));
  return 0;
}
