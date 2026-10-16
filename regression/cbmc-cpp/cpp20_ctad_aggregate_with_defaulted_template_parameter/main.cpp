extern "C" void __CPROVER_assert(bool, const char *);
template <class C, class D = C>
struct view
{
  C *p;
};
// N5008 [over.match.class.deduct]: view{s} deduces view<const char>;
// [dcl.spec.auto.deduct]: so does the return type of range
auto range(const char *s)
{
  return view{s};
}
template <class T, class U>
struct same
{
  static constexpr bool value = false;
};
template <class T>
struct same<T, T>
{
  static constexpr bool value = true;
};
static_assert(same<decltype(range("")), view<const char>>::value, "");
struct path
{
  int n;
  template <class S>
  path(S s) : n(convert(range(s)))
  {
  }
  static int convert();
  template <class T>
  static int convert(const T &v)
  {
    return v.p[0];
  }
};
int main()
{
  path p{"a"};
  __CPROVER_assert(p.n == 'a', "converted through the deduced type");
  __CPROVER_assert(p.n == 'b', "WRONG (must FAIL)");
  return 0;
}
