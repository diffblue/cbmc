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
template <class... Args>
struct direct
{
  // [temp.variadic]/5: one argument per element of the type pack
  typedef decltype(g(declval<Args>()...)) type;
  typedef decltype(g(Args()...)) type2;
  typedef decltype(g(static_cast<Args>(0)..., 1)) type3;
};
template <class, class... Args>
struct probe
{
  static constexpr int n = -1;
};
template <class... Args>
struct probe<decltype(g(declval<Args>()...)), Args...>
{
  static constexpr int n = 100;
};
int main()
{
  __CPROVER_assert(
    direct<int, char>::type::value == 2 &&
      direct<int, char>::type2::value == 2 &&
      direct<int, char>::type3::value == 3 && direct<>::type::value == 0,
    "member typedefs");
  __CPROVER_assert(
    probe<count_of<int, int>, int, int>::n == 100 &&
      probe<count_of<int>, int>::n == 100 &&
      probe<count_of<int>, int, int>::n == -1,
    "partial specialization pattern");
  __CPROVER_assert(direct<int, char>::type::value == 1, "WRONG (must FAIL)");
}
