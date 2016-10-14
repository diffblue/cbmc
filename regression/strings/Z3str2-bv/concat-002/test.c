#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  unsigned int i;
  __CPROVER_string x;
  __CPROVER_string y;
  __CPROVER_string z;

  if (__CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_concat(x, y), z), __CPROVER_string_literal("teest"))
      && __CPROVER_string_equal(y, __CPROVER_string_literal("es"))
      && (i == 15)) {
    assert(0);
  }
  return 0;
}
