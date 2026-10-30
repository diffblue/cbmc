// N5008 [over.match.class.deduct]/3-4: CTAD through alias templates in a
// namespace: a pattern repeating its parameter, a constructor-derived guide,
// a functional cast.  g++ 13 accepts it; clang++ 18 lacks alias CTAD.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct P
{
  T a;
  U b;
};
template <class T>
struct W
{
  T v;
  W(T x) : v(x)
  {
  }
};
namespace lib
{
template <class T>
using same = P<T, T>;
template <class T>
using wrap = W<T>;
} // namespace lib
template <class T, class U>
inline constexpr bool is_same_v = false;
template <class T>
inline constexpr bool is_same_v<T, T> = true;
int main()
{
  lib::same s{1, 2};
  __CPROVER_assert(is_same_v<decltype(s), P<int, int>>, "repeated parameter");
  lib::wrap w(2.5);
  __CPROVER_assert(is_same_v<decltype(w), W<double>>, "constructor guide");
  auto c = lib::wrap{7L};
  __CPROVER_assert(is_same_v<decltype(c), W<long>>, "functional cast");
  __CPROVER_assert(s.a + s.b == 3 && c.v == 7, "values");
  __CPROVER_assert(w.v == 2.0, "WRONG (must FAIL)");
  return 0;
}
