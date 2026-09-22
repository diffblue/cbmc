// N5008 [dcl.type.auto.deduct]/4, [temp.deduct.call]/1, [expr.type]/1: the
// type deduced for `auto' is the type of the initializer expression, which is
// never a reference type -- `auto c = static_cast<T &&>(a)' declares an
// object of type T, not a reference to a.  The front end, which represents a
// reference-typed expression as a marked pointer, deduced the reference and
// made c an alias of a.
extern "C" void __CPROVER_assert(bool, const char *);
struct res
{
  int v;
  res(int x) : v(x)
  {
  }
  ~res()
  {
  }
};
int main()
{
  res a(1);
  auto c = static_cast<res &&>(a);
  c.v = 5;
  __CPROVER_assert(a.v == 1, "c is a distinct object");
  int i = 3;
  auto j = static_cast<int &&>(i);
  j = 4;
  __CPROVER_assert(i == 3, "scalar: a distinct object as well");
  int &ri = i;
  auto k = ri; // an lvalue of reference type: int
  k = 9;
  __CPROVER_assert(i == 3, "auto drops the reference of an lvalue too");
  return 0;
}
