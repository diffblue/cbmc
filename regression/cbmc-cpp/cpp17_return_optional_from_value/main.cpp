// C++17: copy-initializing a std::optional<T> from a T value
// (the canonical `return v;` into an `optional<T>` return type).
//
// This exercises std::optional's converting constructor
//   template<typename _Up = _Tp, _Requires<...> = true>
//   optional(_Up&& __t);
// whose SFINAE constraint `_Requires<...>` references the CLASS
// template parameter `_Tp` (e.g., `is_constructible<_Tp, _Up>`).
//
// CBMC deduces a member constructor template inside an instantiated
// class template by pre-populating the template map with the class's
// template arguments, looking the class up by its tag-type symbol
// name.  The name was reconstructed by prepending "tag-" to the
// front of the enclosing class's qualified name
// (`tag-std::optional<int>`).  But a tag type's symbol name carries
// the "tag-" prefix immediately before the UNQUALIFIED class name,
// after the namespace qualification (`std::tag-optional<int>`).  For
// any namespaced class template — i.e., everything in `std` — the
// reconstructed name did not exist, the class arguments were never
// bound, `_Tp` stayed unresolved, the converting-constructor
// deduction was rejected, and the conversion failed with the
// spurious
//   invalid implicit conversion from 'T' to 'struct optional'.
//
// Verified at the goto-program level: a correctly-elaborated
// std::optional<int> exceeds symbolic-execution memory limits, but
// the goto program must show the converting constructor being
// invoked with the int rvalue (proving the conversion now succeeds).

#include <optional>

std::optional<int> make_opt(int x)
{
  return x;
}

int main()
{
  return make_opt(7).has_value() ? 0 : 1;
}
