#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string Y1;
  __CPROVER_string Y2;
  __CPROVER_string Y3;
  __CPROVER_string Y4;
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, Y1), __CPROVER_string_concat(Y2, y))
      && __CPROVER_string_equal(__CPROVER_string_concat(y, Y3), __CPROVER_string_concat(Y4, x))) {
    assert(0);
  }
  return 0;
}
