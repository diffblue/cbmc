// C++20 three-way comparison (spaceship operator)
#include <compare>

struct Point
{
  int x, y;
  auto operator<=>(const Point &) const = default;
};

int main()
{
  Point a{1, 2}, b{1, 3};
  __CPROVER_assert(a < b, "less than");
  __CPROVER_assert(!(a > b), "not greater");
}
