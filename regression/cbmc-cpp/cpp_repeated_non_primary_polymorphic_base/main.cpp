extern "C" void __CPROVER_assert(bool, const char *);
struct X
{
  virtual int x() const
  {
    return 7;
  }
};
struct A
{
  int i = 0;
  virtual int f() const
  {
    return 10 + i;
  }
};
struct B : X, A
{
  int f() const override
  {
    return 20 + i;
  }
};
struct C : X, A
{
};
struct D : B, C
{
  int x() const override
  {
    return 8;
  }
};
int main()
{
  D d;
  d.B::i = 1;
  d.C::i = 2;
  A &ab = static_cast<B &>(d);
  A &ac = static_cast<C &>(d);
  X &xb = static_cast<B &>(d);
  X &xc = static_cast<C &>(d);
  __CPROVER_assert(ab.f() == 21, "B's overrider");
  __CPROVER_assert(ac.f() == 12, "A's own in C's A");
  __CPROVER_assert(xb.x() == 8 && xc.x() == 8, "D's x in both X");
  D e = d;
  A &eac = static_cast<C &>(e);
  __CPROVER_assert(eac.f() == 12, "copy keeps both A subobjects");
  __CPROVER_assert(ac.f() == 21, "WRONG (must FAIL)");
}
