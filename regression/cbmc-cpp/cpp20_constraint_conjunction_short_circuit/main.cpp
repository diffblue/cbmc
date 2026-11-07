extern "C" void __CPROVER_assert(bool, const char *);
template <typename F, typename T>
inline constexpr bool conv_v = __is_convertible(F, T);
template <typename T>
struct ref_of;
template <typename T>
struct ref_of<T &>
{
  using type = T &;
};
template <typename T>
using ref_of_t = typename ref_of<T>::type;
template <typename T, int Bullet = 1>
struct pick : pick<T, Bullet + 1>
{
};
// [temp.constr.op]/2: the second operand of the conjunction is not
// substituted into when the first is not satisfied
template <typename T>
  requires requires { typename ref_of_t<T>; } && conv_v<ref_of_t<T>, T>
struct pick<T, 1>
{
  static constexpr int value = 1;
};
template <typename T>
struct pick<T, 2>
{
  static constexpr int value = 2;
};
int main()
{
  __CPROVER_assert(pick<int &>::value == 1, "first satisfied");
  __CPROVER_assert(pick<int>::value == 2, "first not satisfied");
  __CPROVER_assert(pick<int>::value == 1, "WRONG (must FAIL)");
}
