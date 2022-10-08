#include <stdbool.h>

bool util_func(int a)
  // clang-format off
  __CPROVER_ensures(
    __CPROVER_return_value == true || __CPROVER_return_value == false)
// clang-format on
{
  if(a > 0)
  {
    return true;
  }
  else
  {
    return false;
  }
}

int test1(int a);
int test2(int a);
