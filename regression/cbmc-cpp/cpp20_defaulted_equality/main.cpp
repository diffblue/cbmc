// C++20 defaulted comparison operators
struct Point
{
  int x;
  int y;
  bool operator==(const Point &) const = default;
  bool operator!=(const Point &) const = default;
};

int main()
{
  Point a = {1, 2};
  Point b = {1, 2};
  Point c = {3, 4};
  __CPROVER_assert(a == b, "equal points");
  __CPROVER_assert(!(a == c), "unequal points");
  __CPROVER_assert(a != c, "not-equal operator");
  __CPROVER_assert(!(a != b), "not not-equal");
  return 0;
}
