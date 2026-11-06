// N5008 [expr.spaceship], [class.compare.default]: defaulted three-way
// comparison.
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int x, y;
  // clang-format 18 splits <=> in C++17 mode
  // clang-format off
  auto operator<=>(const P &) const = default;
  // clang-format on
};
int main()
{
  P a{1, 2}, b{1, 3};
  __CPROVER_assert(a < b && !(a == b), "defaulted three-way comparison");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
