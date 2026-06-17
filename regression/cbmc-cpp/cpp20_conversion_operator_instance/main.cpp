// Mutually-convertible class types that each have a templated integral
// constructor, an explicit converting constructor taking the other type, and a
// templated integral conversion operator (a minimal model of libstdc++'s
// std::ranges::__detail::__max_size_type / __max_diff_type).
//
// After constructing MS from an MD, reading the value back through the
// templated conversion operator `(int)ms` must resolve.  When deducing a
// conversion (e.g. md -> int while matching a constructor candidate), the
// front end had already instantiated the source class's templated conversion
// operator `operator(signed_int)` as a class component; that instance is not
// registered in the class cpp_scope under a name-resolvable key (instantiated
// conversion operators are invoked directly, see deduce_conversion_template).
// The non-template branch of user_defined_conversion_sequence nevertheless
// iterated that component and built a *name*-driven member call, which threw
// "symbol 'operator(signed_int)' is unknown", aborting the enclosing
// statement.
//
// Per [over.match.conv] with [temp.deduct]/8, such an instantiated template
// conversion function is not a viable *non-template* candidate; failing to
// form its call is a soft non-viability handled by the subsequent fresh
// template deduction, not a hard error.
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
  unsigned long _M_val = 0;
  MD() = default;
  template <typename T>
    requires std::integral<T>
  constexpr MD(T i) noexcept : _M_val(i)
  {
  }
  constexpr explicit MD(const MS &dd) noexcept : _M_val(dd._M_val)
  {
  }
  template <typename T>
    requires std::integral<T>
  constexpr explicit operator T() const noexcept
  {
    return _M_val;
  }
};
constexpr MS::MS(const MD &dd) noexcept : _M_val(dd._M_val)
{
}
} // namespace d
int main()
{
  d::MD md{5};
  d::MS ms(md);
  __CPROVER_assert((int)ms == 5, "MD->MS then conversion-operator readback");
  return 0;
}
