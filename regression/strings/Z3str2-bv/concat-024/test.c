#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string m;
  __CPROVER_string n;
  __CPROVER_string x;
  __CPROVER_string y;

  if (__CPROVER_string_equal(__CPROVER_string_concat(x, y), __CPROVER_string_concat(m, n))) {
    assert(0);
  }
  return 0;
}
