extern "C" void __CPROVER_assert(bool, const char *);
// cvise reduction of libstdc++ 16's common_reference<int &, long &>
template <typename T>
constexpr bool is_long = __is_same(T, long);
template <typename T, typename U>
struct is_same_c
{
  static const bool value = __is_same(T, U);
};
template <typename, typename Y>
using cond_res = Y;
template <typename, typename, int = 1>
struct impl;
// [temp.spec.partial.match]/1, [temp.constr.decl]: a constrained partial
// specialization, selected for impl<int, long>
template <typename T1, typename T2>
  requires requires { typename cond_res<T1, T2>; }
struct impl<T1, T2>
{
  using type = cond_res<T1, T2>;
};
int main()
{
  __CPROVER_assert(
    is_same_c<impl<int, long>::type, long>::value, "class template argument");
  __CPROVER_assert(
    is_long<impl<int, long>::type>, "variable template argument");
  __CPROVER_assert(!is_long<impl<int, long>::type>, "WRONG (must FAIL)");
}
