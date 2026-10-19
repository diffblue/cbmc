extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct ident
{
  using type = T;
};
// N5008 [temp.deduct.call]/1: for a function parameter pack with a compound
// pattern, each argument deduces the next element of the pack from that
// pattern -- T = <int, double> for `T *...' and arguments `int *',
// `double *' (the MSVC STL's _Meta_at_impl::_Eval)
template <class... T>
int count(void *, T *...)
{
  return sizeof...(T);
}
template <class T, class... Ts>
T first(void *, T *, Ts *...);
// [temp.variadic]/5: the element is substituted into the pattern, keeping
// its cv-qualifiers
template <class... T>
int by_const_ref(const T &...t)
{
  return sizeof...(T);
}
int main()
{
  int *i = nullptr;
  double *d = nullptr;
  ident<int> *a = nullptr;
  ident<double> *b = nullptr;
  using R = decltype(first(nullptr, b, a));
  __CPROVER_assert(
    count(nullptr, i, d) == 2 && sizeof(R::type) == sizeof(double) &&
      by_const_ref(1) == 1,
    "elements deduced from the pattern");
  __CPROVER_assert(count(nullptr, i, d) == 1, "WRONG (must FAIL)");
  return 0;
}
