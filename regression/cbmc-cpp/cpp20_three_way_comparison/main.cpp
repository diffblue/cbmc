#if !defined(_MSC_VER) && __has_include(<compare>)
// C++20 three-way comparison (spaceship operator)
#  include <compare>

struct Point
{
  int x, y;
  // clang-format 18 splits <=> in C++17 mode
  // clang-format off
  auto operator<=>(const Point &) const = default;
  // clang-format on
};

int main()
{
  Point a{1, 2}, b{1, 3};
  __CPROVER_assert(a < b, "less than");
  __CPROVER_assert(!(a > b), "not greater");
}

#else
int main()
{
}
#endif
