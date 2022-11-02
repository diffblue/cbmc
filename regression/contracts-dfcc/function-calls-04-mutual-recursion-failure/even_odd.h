#include <stdbool.h>
bool odd(int i);
bool even(int i) __CPROVER_requires(0 <= i && i <= 40)
  __CPROVER_ensures(__CPROVER_return_value == (i % 2 == 0))
{
  // patch infinite recursion bug introduced by odd and make sure even still
  // works
  if(i == 42)
    i = 2;

  if(i == 0)
    return true;

  // BUG: add spurious offset
  return odd(i == 11 ? i - 2 : i - 1);
}

bool odd(int i) __CPROVER_requires(0 <= i && i <= 40)
  __CPROVER_ensures(__CPROVER_return_value == (i % 2 != 0))
{
  if(i == 0)
    return false;

  // BUG: call even outside of its preconditions
  // BUG: break monotonous decrease and potentially cause infinite recursion
  return even(i == 13 ? 42 : i - 1);
}
