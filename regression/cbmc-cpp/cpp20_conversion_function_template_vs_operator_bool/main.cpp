#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept integral = std::is_integral_v<T>;
template <class T>
concept is_int128 =
  std::is_same_v<T, __int128> || std::is_same_v<T, unsigned __int128>;
struct point
{
  int x;
};
struct big
{
  unsigned __int128 val;
  template <class T>
    requires integral<T> ||
    is_int128<T> constexpr explicit operator T() const noexcept
  {
    return val;
  }
  constexpr explicit operator bool() const noexcept
  {
    return val != 0;
  }
};
int take_point(const point &p)
{
  return p.x;
}
int take_long(long v)
{
  return static_cast<int>(v);
}
int main()
{
  big b{5};
  __CPROVER_assert(
    static_cast<int>(b) == 5, "explicit conversion to a satisfying type");
  __CPROVER_assert(
    static_cast<unsigned __int128>(b) == 5,
    "explicit conversion to unsigned __int128");
  __CPROVER_assert(bool(b), "contextual conversion to bool");
  point p{7};
  // overload resolution on a call with a `point' never considers big's
  // conversion function template for point (constraint unsatisfied)
  __CPROVER_assert(take_point(p) == 7, "unrelated class type");
  __CPROVER_assert(static_cast<int>(b) == 6, "WRONG (must FAIL)");
}
