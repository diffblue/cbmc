#include <stdbool.h>
bool odd(int i);
bool even(int i) __CPROVER_requires(0 <= i && i <= 40)
  __CPROVER_ensures(__CPROVER_return_value == (i % 2 == 0))
{
  if(i == 0)
    return true;
  return odd(i - 1);
}

bool odd(int i) __CPROVER_requires(0 <= i && i <= 40)
  __CPROVER_ensures(__CPROVER_return_value == (i % 2 != 0))
{
  if(i == 0)
    return false;
  return even(i - 1);
}
