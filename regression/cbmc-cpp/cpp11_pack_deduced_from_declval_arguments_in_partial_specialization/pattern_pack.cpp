extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&declval();
template <class... A>
struct count_of
{
  static constexpr int value = sizeof...(A);
};
struct f
{
  template <class U, class... A>
  count_of<A...> call(U, A...);
};
template <class, class... Args>
struct probe
{
  static constexpr int n = -1;
};
template <class... Args>
struct probe<decltype(declval<f>().call(declval<Args>()...)), Args...>
{
  static constexpr int n = 100;
};
static_assert(
  decltype(declval<f>().call(1, 2, 3))::value == 2,
  "direct: two in the pack");
static_assert(
  probe<count_of<int, int>, int, int, int>::n == 100,
  "pack expanded in the pattern");
int main()
{
  __CPROVER_assert(
    probe<count_of<int, int>, int, int, int>::n == 100,
    "specialization selected");
  __CPROVER_assert(
    probe<count_of<int, int>, int, int, int>::n == -1, "WRONG (must FAIL)");
}
