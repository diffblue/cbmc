extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int a0;
  int a1;
};
struct X
{
  char pad[12];
};
struct B : X, A
{
  int b;
};
template <int A::*P>
int read_via_template(const A &x)
{
  return x.*P;
}
int A::*global_null; // [basic.start.static]/2: zero-initialized, i.e. null
int main()
{
  A x{1, 2};
  B y;
  y.a0 = 10;
  y.a1 = 11;
  y.b = 12;
  int A::*p0 = &A::a0; // offset 0, still not null ([conv.mem]/1)
  int A::*p1 = &A::a1;
  int A::*pn = nullptr;
  int B::*q = p1; // [conv.mem]/2: refers to B's A subobject member
  int B::*qb = &B::b;
  __CPROVER_assert(x.*p0 == 1 && x.*p1 == 2, "read");
  __CPROVER_assert(
    p0 && !pn && !global_null && p0 != pn, "null member pointer");
  __CPROVER_assert(p0 != p1 && p1 == &A::a1, "comparison");
  x.*p1 = 5;
  A *px = &x;
  __CPROVER_assert(x.a1 == 5 && px->*p1 == 5, "write, ->*");
  int B::*q2 = &A::a1;
  int B::*qn = pn; // the null member pointer stays null
  __CPROVER_assert(y.*p1 == 11 && y.*q == 11 && y.*qb == 12, "derived object");
  __CPROVER_assert(q == q2 && q != qb && !qn, "converted comparisons");
  const A cx{7, 8};
  __CPROVER_assert(cx.*p1 == 8, "const object");
  __CPROVER_assert(read_via_template<&A::a1>(cx) == 8, "template argument");
  __CPROVER_assert(x.*p0 == 2, "WRONG (must FAIL)");
}
