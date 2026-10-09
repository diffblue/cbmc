// C++20: relational operators derived from defaulted spaceship
struct Point
{
  int x, y;
  auto operator<=>(const Point &) const = default;
};

int main()
{
  Point a{1, 2}, b{1, 3}, c{1, 2};
  __CPROVER_assert(a < b, "a < b");
  __CPROVER_assert(b > a, "b > a");
  __CPROVER_assert(a <= c, "a <= c");
  __CPROVER_assert(a >= c, "a >= c");
}
