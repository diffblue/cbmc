// C++14 generic lambda with non-int argument types
struct Point
{
  int x;
  int y;
};

int main()
{
  auto identity = [](auto x) { return x; };

  // Call with struct
  Point p = {3, 4};
  Point q = identity(p);
  __CPROVER_assert(q.x == 3, "struct identity x");
  __CPROVER_assert(q.y == 4, "struct identity y");

  // Call with double
  double d = identity(2.5);
  __CPROVER_assert(d > 2.4 && d < 2.6, "double identity");

  // Multi-param generic lambda with mixed types
  auto add = [](auto a, auto b) { return a + b; };
  double r = add(1.5, 2.5);
  __CPROVER_assert(r > 3.9 && r < 4.1, "double add");

  // const auto & parameter
  auto get_x = [](const auto &pt) { return pt.x; };
  int gx = get_x(p);
  __CPROVER_assert(gx == 3, "const ref generic");

  return 0;
}
