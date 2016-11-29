#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string t;
  __CPROVER_string s = __CPROVER_string_concat(t, t);
  __CPROVER_assume(__CPROVER_string_equal(s, __CPROVER_string_literal("aa")));

  assert(__CPROVER_string_equal(t,__CPROVER_string_literal("a")));
  assert(!__CPROVER_string_equal(t,__CPROVER_string_literal("a")));
  // Warning the following does not express the same thing, because
  // equality can fail while the two sides represent the same thing:
  //assert(t  == __CPROVER_string_literal("a"));
  //assert(t != __CPROVER_string_literal("a"));
  return 0;
}
