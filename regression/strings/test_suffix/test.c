#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s;

  __CPROVER_assume(__CPROVER_string_equal(s, __CPROVER_string_literal("pippo")));

  assert(__CPROVER_string_issuffix(__CPROVER_string_literal("po"),s));
  assert(__CPROVER_string_issuffix(__CPROVER_string_literal("pp"),s));

  return 0;
}
