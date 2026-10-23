extern "C" void __CPROVER_assert(bool, const char *);
int ctor_v, dtor_v, dtor_b1, dtor_b2, dtor_d;
struct V
{
  int v;
  V() : v(1)
  {
    ctor_v++;
  }
  virtual ~V()
  {
    dtor_v++;
  }
  virtual int f()
  {
    return 10;
  }
  virtual int g()
  {
    return 20;
  }
};
struct B1 : virtual V
{
  int b1;
  B1() : b1(2)
  {
    v += 100;
  }
  ~B1()
  {
    dtor_b1++;
  }
  int f() override
  {
    return 11;
  }
};
struct B2 : virtual V
{
  int b2;
  B2() : b2(3)
  {
    v += 1000;
  }
  ~B2()
  {
    dtor_b2++;
  }
  int g() override
  {
    return 21 + b2;
  }
};
struct D : B1, B2
{
  int d;
  D() : d(4)
  {
  }
  ~D()
  {
    dtor_d++;
  }
  int f() override
  {
    return 12 + v;
  }
};
int via_v(V *p)
{
  return p->f() * 1000 + p->g();
}
int via_b1(B1 *p)
{
  return p->v;
}
int via_b2(B2 &r)
{
  return r.v + r.f();
}
int main()
{
  {
    D o;
    __CPROVER_assert(ctor_v == 1, "V constructed once");
    __CPROVER_assert(o.v == 1101, "both bases updated the single V");
    __CPROVER_assert(via_b1(&o) == 1101, "V member through B1*");
    __CPROVER_assert(
      via_b2(o) == 1101 + 12 + 1101, "V member and override through B2&");
    V *pv = &o;
    __CPROVER_assert(
      via_v(pv) == (12 + 1101) * 1000 + 21 + 3, "dispatch through V*");
    B2 *pb2 = &o;
    V *pv2 = pb2;
    __CPROVER_assert(pv2 == pv, "B2* -> V* reaches the same V subobject");
    __CPROVER_assert(
      (char *)pv - (char *)&o == 32,
      "V subobject follows the non-virtual part");
    __CPROVER_assert(sizeof(D) == 48, "sizeof D");
    D *pd = pb2 ? static_cast<D *>(pb2) : nullptr;
    __CPROVER_assert(pd == &o, "downcast B2* -> D*");
    B1 b;
    __CPROVER_assert(b.v == 101 && via_v(&b) == 11 * 1000 + 20, "complete B1");
    __CPROVER_assert(sizeof(B1) == 32, "sizeof B1");
  }
  __CPROVER_assert(
    dtor_d == 1 && dtor_b1 == 2 && dtor_b2 == 1, "derived dtors");
  __CPROVER_assert(dtor_v == 2, "V destroyed once per complete object");
  return 0;
}
