/// \file
/// Use CPROVER C library models without requiring contracts for them.

#include <stdlib.h>

int foo(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == 7)
// clang-format on
{
  int *p = malloc(sizeof(int));
  if(p == NULL)
    return 7;
  *p = 7;
  int result = *p;
  free(p);
  return result;
}

int main(void)
{
  foo();
  return 0;
}
