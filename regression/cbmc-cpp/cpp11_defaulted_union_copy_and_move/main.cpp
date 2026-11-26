extern "C" void __CPROVER_assert(bool, const char *);
// [class.copy.ctor]/15, [class.copy.assign]/13: the defaulted copy/move
// constructor and assignment operator of a union copy its object
// representation
union movable
{
  movable()
  {
  }
  movable(movable &&) = default;
  movable &operator=(movable &&) = default;
  int v;
  char c[4];
};
union copyable
{
  copyable()
  {
  }
  copyable(const copyable &) = default;
  copyable &operator=(const copyable &) = default;
  int v;
  float f;
};
int main()
{
  movable a, b;
  b.v = 7;
  a = static_cast<movable &&>(b);
  __CPROVER_assert(a.v == 7, "move assignment");
  movable m(static_cast<movable &&>(a));
  __CPROVER_assert(m.v == 7, "move construction");
  copyable c, d;
  d.v = 8;
  c = d;
  __CPROVER_assert(c.v == 8, "copy assignment");
  copyable e(d);
  __CPROVER_assert(e.v == 8, "copy construction");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
