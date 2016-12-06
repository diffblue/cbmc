#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s;
  s = __CPROVER_string_literal("pippo");
  assert(__CPROVER_string_equal(s, __CPROVER_string_literal("pippo")));
  assert(__CPROVER_string_equal(s, __CPROVER_string_literal("mippo")));

  return 0;
}
