// C++20 defaulted three-way comparison operator
struct Point
{
  int x;
  int y;
  auto operator<=>(const Point &) const = default;
};

int main()
{
  Point a{1, 2};
  Point b{1, 3};
  __CPROVER_assert((a <= > b) < 0, "defaulted spaceship");
  return 0;
}
