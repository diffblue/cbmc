// N5008 [temp.variadic]/5, [dcl.fct]/2: `-> decltype(f(3, a...))' in a
// member function template expands the function parameter pack like the
// body does.  With two or more elements the trailing-return-type kept the
// unexpanded `a' ("symbol 'a' is unknown") and the call found no match;
// free function templates were handled.  libc++'s
// __perfect_forward_impl::operator() is declared this way.
extern "C" void __CPROVER_assert(bool, const char *);
int f1(int a, long b)
{
  return a * 10 + b;
}
int f(int a, long b, char c)
{
  return a * 100 + b * 10 + c;
}
struct plain
{
  template <class... A>
  auto g1(A &&...a) -> decltype(f1(3, a...))
  {
    return f1(3, a...);
  }
  template <class... A>
  auto g(A... a) -> decltype(f(3, a...))
  {
    return f(3, a...);
  }
  template <class... A>
  static auto s(A &&...a) -> decltype(f(3, a...))
  {
    return f(3, a...);
  }
};
template <class X>
struct cls
{
  template <class... A>
  auto g(A &&...a) -> decltype(f(3, static_cast<A &&>(a)...))
  {
    return f(3, static_cast<A &&>(a)...);
  }
};
int main()
{
  plain p;
  __CPROVER_assert(p.g1(4L) == 34, "one element");
  __CPROVER_assert(p.g(4L, char(5)) == 345, "by value, two");
  __CPROVER_assert(plain::s(4L, char(5)) == 345, "static, two");
  cls<int> c;
  __CPROVER_assert(c.g(4L, char(5)) == 345, "class template, forwarding");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
