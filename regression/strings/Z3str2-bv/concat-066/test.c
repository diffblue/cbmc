#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string I;
  __CPROVER_string J;
  __CPROVER_string X;
  __CPROVER_string Y;

  if (__CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_literal("a"), __CPROVER_string_concat(X, Y)), __CPROVER_string_concat(I, __CPROVER_string_concat(__CPROVER_string_literal("c"), J)))) {
    assert(0);
  }
  return 0;
}
