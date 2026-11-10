extern "C" void __CPROVER_assert(bool, const char *);
// the class comes from a "system header" (as libstdc++'s __shared_count
// does): the front end reports dropped system-header bodies
#line 1 "/usr/include/c++/fake/count.h"
struct count
{
  int *pi;
  count() : pi(nullptr)
  {
  }
  template <class P>
  explicit count(P p) : pi(p)
  {
    // ill-formed for any P that is not a pointer: this constructor
    // template's definition must not be instantiated for an overload
    // resolution probe that cannot select it
    *p = *p + 1;
  }
  friend bool operator==(const count &a, const count &b) noexcept
  {
    return a.pi == b.pi;
  }
};
#line 20 "main.cpp"
struct point
{
  int x, y;
};
bool operator==(const point &a, const point &b)
{
  return a.x == b.x && a.y == b.y;
}
enum colour
{
  red,
  green
};
int main()
{
  point p{1, 2}, q{1, 2};
  __CPROVER_assert(p == q, "operator== of point, not a conversion to count");
  colour c = red;
  __CPROVER_assert(c == red, "built-in enum comparison");
  count k;
  int v = 3;
  count heap(&v);
  __CPROVER_assert(
    !(k == heap) && v == 4,
    "count's own operator== and the explicit constructor");
  __CPROVER_assert(p.x == 2, "WRONG (must FAIL)");
}
