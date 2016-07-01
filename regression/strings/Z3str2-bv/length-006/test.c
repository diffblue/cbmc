#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;
  __CPROVER_string y;

  if ((__CPROVER_string_length(__CPROVER_string_concat(x, y)) == 1)) {
    assert(0);
  }
  return 0;
}
