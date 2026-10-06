// N5008 [temp.variadic]/5.2, /7: a base-specifier pack expansion over an
// empty pack produces no base-specifier, so a constructor need not
// initialize any base (leaf has no default constructor)
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct leaf
{
  T v;
  template <class U>
  leaf(U &&u) : v(u)
  {
  }
};
template <class...>
struct impl;
template <class... T>
struct impl<int, T...> : leaf<T>...
{
  int n;
  impl(int k) : n(k)
  {
  }
};
template <class... T>
struct impl2 : leaf<T>...
{
  int n;
  impl2(int k) : n(k)
  {
  }
  template <class... U>
  impl2(int k, U &&...u) : leaf<T>(u)..., n(k)
  {
  }
};
int main()
{
  impl<int> a(3);
  impl2<> b(4);
  impl2<long> c(5, 6);
  __CPROVER_assert(a.n == 3 && b.n == 4, "empty pack");
  __CPROVER_assert(c.n == 5 && c.v == 6, "one element");
  __CPROVER_assert(b.n == 3, "WRONG (must FAIL)");
}
