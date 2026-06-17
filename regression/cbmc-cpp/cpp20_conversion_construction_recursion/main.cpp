// Mutually-convertible class types that each provide a templated integral
// constructor and an explicit converting constructor taking the other type
// (a minimal model of libstdc++'s std::ranges::__detail::__max_size_type /
// __max_diff_type).  Constructing MS from an MD -- exactly what
// __to_unsigned_like does with __max_size_type(__t) -- must resolve to the
// explicit converting constructor without recursing without bound.
//
// The recursion arises because the templated constructor MS(T)/MD(T) is
// considered with T deduced as the *other class type*; that produces a bogus
// by-value constructor whose argument has to be materialised by constructing
// the same type again, ad infinitum.  Per [temp.deduct]/5 with
// [temp.constr.decl]/1, a function-template specialisation whose associated
// constraints (here `requires std::integral<T>`) are not satisfied by the
// deduced arguments is removed from the candidate set -- integral<MD> is
// false, so MS(T = MD) is not viable and the recursion does not occur.
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
};
class MD
{
public:
  unsigned long _M_val = 0;
  MD() = default;
  template <typename T>
  requires std::integral<T> constexpr MD(T i) noexcept : _M_val(i)
  {
  }
  constexpr explicit MD(const MS &dd) noexcept : _M_val(dd._M_val)
  {
  }
};
constexpr MS::MS(const MD &dd) noexcept : _M_val(dd._M_val)
{
}
} // namespace d
int main()
{
  d::MD md{5};
  d::MS ms(md); // MD -> MS construction (as __to_unsigned_like does)
  __CPROVER_assert(ms._M_val == 5, "MD->MS construction preserves value");
  return 0;
}
