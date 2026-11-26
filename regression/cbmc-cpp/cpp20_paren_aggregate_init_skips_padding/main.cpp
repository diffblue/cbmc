// N5008 [dcl.init.general]/16.6.2.2 (C++20), [dcl.init.aggr]/2: `A a(1, 2.0)'
// initializes the elements x and y of the aggregate A in order.  Layout
// padding is not an element; the front end counted the padding after x and
// assigned 2.0 to it, leaving y zero.
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int x;
  double y;
};
struct I
{
  int x;
  int y;
};
int main()
{
  A a(1, 2.0);
  I i(3, 4);
  A b(5);
  __CPROVER_assert(a.x == 1 && a.y == 2.0, "padding skipped");
  __CPROVER_assert(i.x == 3 && i.y == 4, "no padding");
  __CPROVER_assert(b.x == 5 && b.y == 0, "missing element value-initialized");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
