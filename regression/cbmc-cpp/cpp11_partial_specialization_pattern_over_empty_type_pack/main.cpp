extern "C" void __CPROVER_assert(bool, const char *);
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
// [temp.spec.partial.match]/2, [temp.variadic]/5: Args is deduced from the
// trailing arguments; with Args empty, `g(declval<Args>()...)' is `g()'
template <class... Args>
struct probe<decltype(g(declval<Args>()...)), Args...>
{
  static constexpr int n = 100;
};
int main()
{
  __CPROVER_assert(probe<count_of<int>, int>::n == 100, "one element");
  __CPROVER_assert(probe<count_of<>>::n == 100, "empty pack");
  __CPROVER_assert(probe<count_of<int>>::n == -1, "no match");
  __CPROVER_assert(probe<count_of<>>::n == -1, "WRONG (must FAIL)");
}
