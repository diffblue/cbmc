// N5008 [expr.dynamic.cast]/8: dynamic_cast<void *>(v) for a pointer to a
// polymorphic class is a pointer to the most derived object.
extern "C" void __CPROVER_assert(bool, const char *);
struct X
{
  int x;
  virtual ~X() = default;
};
struct Y
{
  int y;
  virtual ~Y() = default;
};
struct Z : X, Y
{
};
int main()
{
  Z z;
  Y *p = &z;
  __CPROVER_assert(dynamic_cast<void *>(p) == (void *)&z, "most derived");
  __CPROVER_assert(dynamic_cast<void *>(p) == (void *)p, "WRONG (must FAIL)");
}
