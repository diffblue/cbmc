// [temp.deduct]/5 with [temp.constr.decl]/1: after argument deduction for a
// conversion-function *template* ([temp.deduct.conv]), its associated
// constraints (requires-clause) must be satisfied with the deduced arguments;
// an unsatisfied constraint is a deduction failure, so the candidate is removed
// rather than instantiated.
//
// This mirrors libstdc++'s mutually-recursive std::ranges::__detail
// __max_size_type / __max_diff_type, each with a constrained templated
// conversion operator (template<typename _Tp> requires integral<_Tp> ||
// __is_int128<_Tp> operator _Tp()).  Deducing that operator for a *class*
// destination (the other max-width type) must be rejected by the constraint;
// otherwise the front end instantiates a bogus "operator <class>" and fails.
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
constexpr MS::MS(const MD &dd) noexcept : _M_val(dd._M_rep._M_val)
{
}
}

int main()
{
  d::MD md{5};
  int x = (int)md;
  __CPROVER_assert(x == 5, "constrained templated conversion operator");
  return 0;
}
