#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string X;
  __CPROVER_string ts0;
  __CPROVER_string ts1;
  __CPROVER_string ts2;

  if (__CPROVER_string_equal(X, __CPROVER_string_concat(ts0, __CPROVER_string_concat(__CPROVER_string_literal("abc"), ts2)))
      && __CPROVER_string_equal(X, __CPROVER_string_literal("abc"))) {
    assert(0);
  }
  return 0;
}
