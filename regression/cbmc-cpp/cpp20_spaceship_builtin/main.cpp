// C++20 built-in spaceship operator on primitive types
// [expr.spaceship]/8: the comparison category types come from <compare>
#include <compare>
int main()
{
  int a = 1, b = 2;
  __CPROVER_assert((a <=> b) < 0, "1 < 2");
  __CPROVER_assert((b <=> a) > 0, "2 > 1");
  __CPROVER_assert((a <=> a) == 0, "1 == 1");
  return 0;
}
