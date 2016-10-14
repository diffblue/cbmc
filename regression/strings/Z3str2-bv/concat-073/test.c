#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string M;
  __CPROVER_string X;
  __CPROVER_string Y1;
  __CPROVER_string Y2;
  __CPROVER_string Z;

  if (__CPROVER_string_equal(Z, __CPROVER_string_concat(X, __CPROVER_string_literal("gkhi")))
      && __CPROVER_string_equal(Z, __CPROVER_string_concat(Y1, Y2))
      && __CPROVER_string_equal(Z, __CPROVER_string_concat(__CPROVER_string_literal("abcd"), M))) {
    assert(0);
  }
  return 0;
}
