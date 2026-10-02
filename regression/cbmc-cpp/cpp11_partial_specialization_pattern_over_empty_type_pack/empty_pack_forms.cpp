extern "C" void __CPROVER_assert(bool, const char *);
// [temp.spec.partial.match]/2, [temp.deduct.type]/9: a trailing pack deduced
// from no arguments is empty, in the plain, the template-id and the
// decltype pattern
template <class T>
T &&declval();
template <class... A>
struct count_of
{
  static constexpr int value = sizeof...(A);
};
template <class... A>
count_of<A...> g(A...);
template <class, class... Args>
struct probe
{
  static constexpr int n = -1;
};
template <class... Args>
struct probe<int, Args...>
{
  static constexpr int n = 1;
};
template <class, class... Args>
struct p2
{
  static constexpr int n = -1;
};
template <class... Args>
struct p2<count_of<Args...>, Args...>
{
  static constexpr int n = 2;
};
template <class, class... Args>
struct p3
{
  static constexpr int n = -1;
};
template <class... Args>
struct p3<decltype(g(declval<Args>()...)), Args...>
{
  static constexpr int n = 3;
};
template <class, class... Args>
struct p4
{
  static constexpr int n = -1;
};
template <class... Args>
struct p4<decltype(g()), Args...>
{
  static constexpr int n = 4;
};
int main()
{
  __CPROVER_assert(probe<int>::n == 1, "plain empty");
  __CPROVER_assert(p2<count_of<>>::n == 2, "pack in first arg");
  __CPROVER_assert(p3<count_of<>>::n == 3, "decltype pack");
  __CPROVER_assert(p4<count_of<>>::n == 4, "decltype non-dependent");
  __CPROVER_assert(p3<count_of<>>::n != 3, "WRONG (must FAIL)");
}
