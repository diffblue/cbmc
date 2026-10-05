// N5008 [over.match.best]/2.5, [temp.func.order]: of two equally good
// function template specializations, the more specialized template wins;
// how many template arguments each has does not matter
extern "C" void __CPROVER_assert(bool, const char *);
template <class C, class T, class A>
struct basic_string
{
  int size = 5;
};
template <class C>
struct string_view
{
  int n;
};
// libstdc++'s filesystem::__detail::__effective_range
template <class C, class T, class A>
string_view<C> effective_range(const basic_string<C, T, A> &s)
{
  return string_view<C>{s.size};
}
template <class Source>
int effective_range(const Source &)
{
  return 1;
}
struct R
{
  int n;
};
template <class C, class T, class A>
R make(const basic_string<C, T, A> &s)
{
  return R{s.size + 1};
}
template <class Source>
int make(const Source &)
{
  return 1;
}
// libstdc++'s __niter_wrap: by value and by reference to const are equally
// good conversions ([over.ics.rank]/3.2.6 compares two reference bindings
// only), so partial ordering decides
template <class From, class To>
int wrap(From, To)
{
  return 2;
}
template <class I>
int wrap(const I &, I)
{
  return 1;
}
// libstdc++'s _Variadic_union: `idx<0>' in a pattern is not deduced, and
// matches only idx<0> ([temp.deduct.type]/1)
template <unsigned long N>
struct idx
{
};
template <class... A>
int pick(idx<0>, A &&...)
{
  return 0;
}
template <unsigned long N, class... A>
int pick(idx<N>, A &&...)
{
  return 10 + N;
}
// std::pair's constructors: binding an rvalue reference to an rvalue is a
// better conversion than binding a reference to const ([over.ics.rank]/3.2.3),
// decided before partial ordering
template <class U = int>
int bind(const int &)
{
  return 1;
}
template <class U>
int bind(U &&)
{
  return 2;
}
int main()
{
  basic_string<char, int, long> name;
  __CPROVER_assert(effective_range(name).n == 5, "more specialized");
  R r = make(name);
  __CPROVER_assert(r.n == 6, "copy-initialization");
  __CPROVER_assert(effective_range(3) == 1, "only the generic one");
  __CPROVER_assert(wrap(r, r) == 1 && wrap(r, 3) == 2, "by reference to const");
  __CPROVER_assert(pick(idx<0>(), 1) == 0, "non-deduced constant");
  __CPROVER_assert(pick(idx<2>(), 1) == 12, "deduced constant");
  int lvalue = 1;
  __CPROVER_assert(bind(3) == 2 && bind(lvalue) == 2, "rvalue reference");
  __CPROVER_assert(r.n == 5, "WRONG (must FAIL)");
}
