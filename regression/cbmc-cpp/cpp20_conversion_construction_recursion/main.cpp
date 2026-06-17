// Mutually-convertible class types that each provide a templated integral
// constructor, a templated integral conversion operator, and an explicit
// converting constructor taking the other type (a minimal model of
// libstdc++'s std::ranges::__detail::__max_size_type / __max_diff_type).
// Constructing MS from an MD -- exactly what __to_unsigned_like does with
// __max_size_type(__t) -- must resolve to the explicit converting
// constructor without recursing into a second user-defined conversion.
//
// [over.ics.user]/1 with [over.best.ics]/4: a user-defined conversion
// sequence consists of an initial standard conversion sequence, a single
// user-defined conversion, and a second standard conversion sequence -- it
// contains at most ONE user-defined conversion.  The argument conversions of
// a candidate constructor must therefore be standard conversion sequences;
// they may not themselves require a user-defined conversion.  Without that
// rule, resolving MD -> MS keeps considering MS's copy/move constructor
// (whose argument would need MD -> MS again), which recurses without bound.
#include <concepts>
namespace d
{
class MD;
class MS
{
public:
  unsigned long _M_val = 0;
  MS() = default;
  template <typename T>
    requires std::integral<T>
  constexpr MS(T i) noexcept : _M_val(i)
  {
  }
  constexpr explicit MS(const MD &dd) noexcept;
  template <typename T>
    requires std::integral<T>
  constexpr explicit operator T() const noexcept
  {
    return _M_val;
  }
};
class MD
{
public:
  MS _M_rep;
  MD() = default;
  template <typename T>
    requires std::integral<T>
  constexpr MD(T i) noexcept : _M_rep(i)
  {
  }
  constexpr explicit MD(const MS &dd) noexcept : _M_rep(dd)
  {
  }
  template <typename T>
    requires std::integral<T>
  constexpr explicit operator T() const noexcept
  {
    return static_cast<T>(_M_rep);
  }
};
constexpr MS::MS(const MD &dd) noexcept
  : _M_val(static_cast<unsigned long>(dd._M_rep))
{
}
} // namespace d
int main()
{
  d::MD md{5};
  d::MS ms(md); // MD -> MS construction (as __to_unsigned_like does)
  __CPROVER_assert((int)ms == 5, "MD->MS construction preserves value");
  return 0;
}
