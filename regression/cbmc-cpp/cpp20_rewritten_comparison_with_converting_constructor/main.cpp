// clang-format off
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
template <class T>
concept integral = std::is_integral_v<T>;
struct big
{
  unsigned long v;
  constexpr big() : v(0)
  {
  }
  template <class T>
    requires integral<T>
  constexpr big(T i) : v(static_cast<unsigned long>(i))
  {
  }
  friend constexpr bool operator==(const big &l, const big &r) noexcept
  {
    return l.v == r.v;
  }
  friend constexpr std::strong_ordering
  operator<=>(const big &l, const big &r) noexcept
  {
    return l.v <=> r.v;
  }
};
constexpr unsigned long bits = 64;
int main()
{
  big r(10);
  __CPROVER_assert(
    r <= bits,
    "rewritten <= with the right operand converted by a constrained "
    "constructor template");
  __CPROVER_assert(
    r != 0 && 5 < r && !(r == 64), "reversed and converted operands");
  __CPROVER_assert(r > bits, "WRONG (must FAIL)");
}
// clang-format on
