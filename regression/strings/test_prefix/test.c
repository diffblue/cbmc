#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s = __CPROVER_string_literal("Hello World!");

  //__CPROVER_assume(__CPROVER_string_equal(s, __CPROVER_string_literal("Hello World!")));

  __CPROVER_bool b = __CPROVER_string_isprefix(__CPROVER_string_literal("Hello"),s);
  __CPROVER_bool c = __CPROVER_string_isprefix(__CPROVER_string_literal("Wello"),s);
  assert(b);
  assert(c);

  return 0;
}
