#include <assert.h>
#include "../../cprover-string-hack.h"

int main()
{
  unsigned int i;
  __CPROVER_string x;

  if ((__CPROVER_string_length(__CPROVER_string_literal("abcd")) == i)
      && ((int)__CPROVER_string_length(x)) > ((int)(i + 1))) {
    assert(0);
  }
  return 0;
}
