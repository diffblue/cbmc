#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string k;
  __CPROVER_string m;
  __CPROVER_string n1;
  __CPROVER_string n2;
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(z, __CPROVER_string_concat(x, __CPROVER_string_literal("gkhi")))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(y, __CPROVER_string_literal("hi")))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(__CPROVER_string_literal("abcd"), m))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(__CPROVER_string_literal("ab"), k))
      && __CPROVER_string_equal(z, __CPROVER_string_concat(n1, n2))) {
    assert(0);
  }
  return 0;
}
