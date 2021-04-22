#include "utility.h"
#include <stdbool.h>
#include <stdlib.h>

int foo(int *x) __CPROVER_requires(s2n_result_is_ok(validity3(x)))
  __CPROVER_assigns(*x) __CPROVER_ensures(
    __CPROVER_return_value == *x + 5 && s2n_result_is_ok(validity3(x)))
{
  *x = *x + 0;
  return *x + 5;
}
