#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  __CPROVER_string x;

  if (((unsigned)3) >= ((unsigned)__CPROVER_string_length(x))) {
    assert(0);
  }
  return 0;
}
