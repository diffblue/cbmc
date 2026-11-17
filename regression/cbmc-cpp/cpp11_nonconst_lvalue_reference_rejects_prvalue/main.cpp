extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.init.ref]/5, [over.ics.ref]/3: a non-const lvalue reference
// binds only to an lvalue; a prvalue argument (T{...}, T(...), a braced
// aggregate) makes such an overload non-viable, so the by-value / const& /
// && overload is selected instead of an "ambiguous" report.
struct S
{
  int a;
  int b;
  S(int x, int y) : a(x), b(y)
  {
  }
};
struct A
{
  int v;
};
int f(S &)
{
  return 1;
}
int f(S)
{
  return 2;
}
int g(S &)
{
  return 1;
}
int g(const S &)
{
  return 2;
}
int h(S &)
{
  return 1;
}
int h(S &&)
{
  return 2;
}
template <class C>
auto t(C &c) -> decltype(c.v, 1)
{
  return 1;
}
int t(A)
{
  return 2;
}
template <class C>
int u(C &c)
{
  return 1;
}
int u(A)
{
  return 2;
}
struct R
{
  template <class C>
  auto z(C &c) -> decltype(c.v, 1)
  {
    return 1;
  }
  int z(A)
  {
    return 2;
  }
};
int main()
{
  __CPROVER_assert(f(S{1, 2}) == 2, "T{}: only by-value viable");
  __CPROVER_assert(f(S(1, 2)) == 2, "T(): only by-value viable");
  __CPROVER_assert(g(S{1, 2}) == 2, "T{}: const S& only");
  __CPROVER_assert(h(S{1, 2}) == 2, "T{}: S&& preferred");
  __CPROVER_assert(
    t(A{1}) == 2,
    "aggregate prvalue: template C& not viable (trailing decltype)");
  __CPROVER_assert(u(A{1}) == 2, "aggregate prvalue: template C& not viable");
  R r;
  __CPROVER_assert(
    r.z(A{1}) == 2, "member template C& not viable for a prvalue");
  S s(3, 4);
  __CPROVER_assert(g(s) == 1 && h(s) == 1, "lvalue binds S&");
  return 0;
}
