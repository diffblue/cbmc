extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int v = 5;
  virtual int g() const
  {
    return v;
  }
};
struct A : virtual V
{
  int i = 0;
  virtual int f() const
  {
    return 10 + i;
  }
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
  int g() const override
  {
    return 40 + v;
  }
};
int main()
{
  D d;
  d.B::i = 1;
  d.C::i = 2;
  A &ab = static_cast<B &>(d);
  A &ac = static_cast<C &>(d);
  __CPROVER_assert(ab.f() == 21, "B's overrider");
  __CPROVER_assert(ac.f() == 12, "A's own in C's A");
  __CPROVER_assert(ab.g() == 45 && ac.g() == 45, "shared V, D's g");
  __CPROVER_assert(&static_cast<V &>(ab) == &static_cast<V &>(ac), "one V");
  __CPROVER_assert(ac.f() == 21, "WRONG (must FAIL)");
}
