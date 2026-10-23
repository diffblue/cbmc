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
  int f() const override
  {
    return 20 + i;
  }
};
struct C : A
{
};
struct D : B, C
{
};
int main()
{
  D d;
  d.B::i = 1;
  d.C::i = 2;
  B &b = d;
  C &c = d;
  A &ab = b;
  A &ac = c;
  // [class.virtual]/2: each A subobject has its own final overrider
  __CPROVER_assert(ab.f() == 21, "B path");
  __CPROVER_assert(ac.f() == 12, "C path");
  __CPROVER_assert(ab.f() == 12, "WRONG (must FAIL)");
}
