#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string X;
  __CPROVER_string Y;

  if (__CPROVER_string_equal(__CPROVER_string_concat(X, __CPROVER_string_concat(__CPROVER_string_literal("ab"), Y)), __CPROVER_string_concat(Y, __CPROVER_string_concat(__CPROVER_string_literal("ba"), X)))
      && (2 == __CPROVER_string_length(X))) {
    assert(0);
  }
  return 0;
}
