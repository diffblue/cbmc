// N5008 [temp.alias]/2, [temp.concept], [temp.variable]: a specialization
// of an alias template, a concept or a variable template is determined by
// its template arguments; CBMC reuses an instance made before.  The same
// specializations are named many times here, also after a substitution
// failure for other arguments (which makes no instance and is not cached),
// and in different scopes.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;
template <class T>
constexpr bool is_int_like = false;
template <>
constexpr bool is_int_like<int> = true;
template <>
constexpr bool is_int_like<long> = true;
template <class T>
concept integral = is_int_like<T>;
template <class T>
constexpr int width_v = sizeof(T) * 8;
template <class T, class = enable_if_t<integral<T>>>
constexpr int f(T)
{
  return 1;
}
constexpr int f(...)
{
  return 2;
}
namespace inner
{
template <class T>
using same = enable_if_t<integral<T>, T>;
constexpr int g(same<int> x)
{
  return x + width_v<int>;
}
} // namespace inner
int main()
{
  static_assert(f(1) == 1 && f(2) == 1);
  static_assert(integral<int> && !integral<double> && integral<int>);
  static_assert(width_v<int> == 32 && width_v<char> == 8 && width_v<int> == 32);
  __CPROVER_assert(
    f(1) + f(1.0) + f(3L) + f(4.0f) == 6 && inner::g(1) == 33 &&
      width_v<short> == 16,
    "reused instances");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
