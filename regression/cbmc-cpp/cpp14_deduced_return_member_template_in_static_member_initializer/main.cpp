extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
inline constexpr bool is_same_v = false;
template <class T>
inline constexpr bool is_same_v<T, T> = true;
template <int N>
struct gen
{
  template <int M>
  static decltype(auto) element(int v)
  {
    return v + M;
  }
  static auto invoke()
  {
    return element<N>(1);
  }
  // N5008 [dcl.spec.auto.general]/12: invoke's and element's return types
  // are deduced from their definitions while gen<2> is instantiated
  static constexpr bool same = is_same_v<decltype(invoke()), int>;
};
int main()
{
  __CPROVER_assert(gen<2>::invoke() == 3, "called");
  __CPROVER_assert(gen<2>::same, "deduced");
  __CPROVER_assert(gen<2>::invoke() == 2, "WRONG (must FAIL)");
  return 0;
}
