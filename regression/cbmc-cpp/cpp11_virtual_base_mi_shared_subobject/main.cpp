extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int v;
  V() : v(1)
  {
  }
};
struct B1 : virtual V
{
  int b1;
  B1() : b1(2)
  {
  }
};
struct B2 : virtual V
{
  int b2;
  B2() : b2(3)
  {
  }
};
struct D : B1, B2
{
  int d;
  D() : d(4)
  {
  }
};
int b2_of(B2 *p)
{
  return p->b2;
}
int v_of(B2 *p)
{
  return p->v;
}
int main()
{
  D o;
  __CPROVER_assert(o.v == 1 && o.b1 == 2 && o.b2 == 3 && o.d == 4, "members");
  B2 *p = &o;
  __CPROVER_assert(b2_of(p) == 3, "B2 member through B2*");
  __CPROVER_assert(v_of(p) == 1, "virtual base member through B2*");
  __CPROVER_assert(
    sizeof(D) == 40, "sizeof D (Itanium: vptr b1 vptr b2 d pad v pad)");
  __CPROVER_assert(sizeof(B1) == 16, "sizeof B1 (vptr, b1, v)");
  return 0;
}
