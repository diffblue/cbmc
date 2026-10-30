extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int i = 0;
  virtual int f() const
  {
    return 10 + i;
  }
  virtual ~A() = default;
};
struct B : A
{
};
struct C : A
{
};
struct D : B, C
{
  // [class.virtual]/2: the final overrider in both A subobjects
  int f() const override
  {
    return 30 + B::i + C::i;
  }
};
int main()
{
  D d;
  d.B::i = 1;
  d.C::i = 2;
  A &ab = static_cast<B &>(d);
  A &ac = static_cast<C &>(d);
  __CPROVER_assert(ab.f() == 33, "B path");
  __CPROVER_assert(ac.f() == 33, "C path");
  __CPROVER_assert(ac.f() == 12, "WRONG (must FAIL)");
}
