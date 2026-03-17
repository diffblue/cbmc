// Verify numeric_limits properties from <limits>
#include <cassert>
#include <climits>
#include <limits>

int nondet_int();

int main()
{
  static_assert(std::numeric_limits<int>::is_integer, "int is integer");
  static_assert(std::numeric_limits<int>::is_signed, "int is signed");

  // runtime verification: nondet value is within int limits
  int x = nondet_int();
  assert(x >= INT_MIN);
  assert(x <= INT_MAX);

  return 0;
}
