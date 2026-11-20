// N5008 [defns.signature.member], [defns.signature.member.templ]: the
// ref-qualifier is part of a member function's signature.
// [over.match.funcs.general]/4,5: the implicit object parameter of an `&'
// member is an lvalue reference and that of an `&&' member an rvalue
// reference; only a member without a ref-qualifier also accepts an rvalue
// object through an lvalue reference.  [over.ics.rank]/3.2.3: for an rvalue
// object, `&&' is better than `const &'.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&mv(T &t)
{
  return static_cast<T &&>(t);
}
struct S
{
  int f() const &
  {
    return 1;
  }
  int f() &&
  {
    return 2;
  }
  int g() const &&
  {
    return 3;
  }
  int g() &
  {
    return 4;
  }
  template <class A>
  int h(A) const &
  {
    return 5;
  }
  template <class A>
  int h(A) &&
  {
    return 6;
  }
};
struct W
{
  template <class A>
  int f(A) &
  {
    return 1;
  }
  template <class A>
  int f(A) &&
  {
    return 2;
  }
  template <class A>
  int f(A) const &
  {
    return 3;
  }
  int k() &;
  int k() &&;
};

int W::k() &
{
  return 7;
}

int W::k() &&
{
  return 8;
}

int main()
{
  S s;
  const S cs{};
  __CPROVER_assert(s.f() == 1 && S().f() == 2 && mv(s).f() == 2, "f");
  __CPROVER_assert(cs.f() == 1 && mv(cs).f() == 1, "const f");
  __CPROVER_assert(s.g() == 4 && S().g() == 3 && mv(cs).g() == 3, "g");
  __CPROVER_assert(s.h(0) == 5 && S().h(0) == 6 && mv(s).h(0) == 6, "h");
  W w;
  const W cw{};
  __CPROVER_assert(w.f(0) == 1 && W().f(0) == 2 && cw.f(0) == 3, "W::f");
  __CPROVER_assert(w.k() == 7 && W().k() == 8, "W::k");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
