// N5008 [defns.signature.member.templ]: a member function template's
// signature includes its cv-qualifiers, so `template <class A> int f(A)'
// and `template <class A> int f(A) const' are two templates
// ([temp.over.link]/6); for a const object only the const one is viable
// ([over.match.funcs.general]/4).
extern "C" void __CPROVER_assert(bool, const char *);

int g(int b, int (&a)[5])
{
  return a[b];
}

struct wrap
{
  int bound;
  template <class A>
  int f(A)
  {
    return 1;
  }
  template <class A>
  int f(A) const
  {
    return 2;
  }
  template <class... A>
  auto h(A &&...a) -> decltype(g(bound, a...))
  {
    return g(bound, a...);
  }
  template <class... A>
  auto h(A &&...a) const -> decltype(g(bound, a...))
  {
    return g(bound, a...) + 10;
  }
};

int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  const wrap cw{2};
  wrap w{2};
  __CPROVER_assert(cw.f(0) == 2 && w.f(0) == 1, "f");
  __CPROVER_assert(cw.h(arr) == 13 && w.h(arr) == 3, "h");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
