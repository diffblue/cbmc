// N5008 [over.ics.list]/6, [dcl.init.list]/3.4, [dcl.init.ref]/5.4.2: a
// braced-init-list argument for a reference-to-array parameter
// (`T (&&)[1]') aggregate-initializes a temporary array and binds the
// reference to it.  libc++'s std::variant narrowing check is
// `decltype(__test_impl<_Dest>({std::declval<_Source>()}))' with
// `__test_impl(_Dest (&&)[1])'; the call had no viable candidate.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct type_identity
{
  using type = T;
};
template <class T>
T &&declval() noexcept;
struct check
{
  template <class D>
  static auto test(D (&&)[1]) -> type_identity<D>;
  template <class D, class S>
  using apply = decltype(test<D>({declval<S>()}));
  template <class D, class S>
  using apply_braced = decltype(test<D>({S{}}));
};
template <class T, class U>
inline constexpr bool same_v = __is_same(T, U);
static_assert(same_v<check::apply<int, int>, type_identity<int>>, "alias");
static_assert(
  same_v<check::apply_braced<long, long>, type_identity<long>>,
  "T{}");
int sum(const int (&a)[3])
{
  return a[0] + a[1] + a[2];
}
int first(int (&&a)[2])
{
  return a[0];
}
int main()
{
  __CPROVER_assert(sum({1, 2, 3}) == 6, "const int (&)[3] from {1, 2, 3}");
  __CPROVER_assert(
    sum({1, 2}) == 3, "[dcl.init.aggr]/5.2: a[2] value-initialized");
  __CPROVER_assert(first({7, 8}) == 7, "int (&&)[2]");
  __CPROVER_assert(sum({1, 2, 3}) == 7, "WRONG (must FAIL)");
}
