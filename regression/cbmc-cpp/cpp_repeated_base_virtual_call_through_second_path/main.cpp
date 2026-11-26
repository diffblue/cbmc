// N5008 [class.virtual]/2, [class.mi]/4: D has two A subobjects (through B
// and through C) sharing one virtual base V.  A virtual call of V::g through
// either A reaches the final overrider D::g.
extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int v = 5;
  virtual int g() const
  {
    return v;
  }
};
int askg(const V &x)
{
  return x.g();
}
struct A : virtual V
{
  int i = 0;
};
struct B : A
{
};
struct C : A
{
};
struct D : B, C
{
  int g() const override
  {
    return 40 + v;
  }
};
int main()
{
  D d;
  __CPROVER_assert(askg(static_cast<B &>(d)) == 45, "through B");
  __CPROVER_assert(askg(static_cast<C &>(d)) == 45, "through C");
  __CPROVER_assert(askg(static_cast<C &>(d)) != 45, "WRONG (must FAIL)");
}
