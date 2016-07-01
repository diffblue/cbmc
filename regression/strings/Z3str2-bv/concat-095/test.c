#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y1;
  __CPROVER_string y2;

  if (__CPROVER_string_equal(x, __CPROVER_string_literal("abc\nefg  "))
      && __CPROVER_string_equal(y1, __CPROVER_string_literal("z_	_z-\t-\\'=\"_z"))) {
    assert(0);
  }
  return 0;
}
