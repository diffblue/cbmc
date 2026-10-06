// N5008 [class.inhctor.init]/1: a constructor inherited by a
// using-declaration initializes the base subobject; the other members are
// initialized as by a defaulted default constructor of the derived class
extern "C" void __CPROVER_assert(bool, const char *);
struct M
{
  int m;
  M() : m(8)
  {
  }
};
struct B
{
  int b;
  B(int x) : b(x)
  {
  }
  B(int *p, int d = 4) : b(*p + d)
  {
    *p = 0;
  }
  B(const char *, long l) : b(int(l))
  {
  }
  virtual int f()
  {
    return 1;
  }
};
struct D : B
{
  using B::B;
  D(const char *, long) : B(-1)
  {
  }
  int k = 3;
  M mm;
  int f() override
  {
    return 2;
  }
};
int main()
{
  D a(5);
  __CPROVER_assert(a.b == 5 && a.k == 3, "default member initializer");
  __CPROVER_assert(a.mm.m == 8, "member default constructor");
  B &r = a;
  __CPROVER_assert(r.f() == 2, "virtual table of the derived class");
  int n = 6;
  D c(&n);
  __CPROVER_assert(c.b == 10 && n == 0, "default argument of the base");
  D h("x", 9L);
  __CPROVER_assert(h.b == -1, "hidden by a constructor of the class");
  __CPROVER_assert(a.k == 0, "WRONG (must FAIL)");
}
