// Regression for the strip-tag bug in
// `cpp_instantiate_template.cpp::instantiate_template`'s
// deferred-method drain.  The class-name used to match deferred
// method ids stripped a leading "tag-" only at position 0, so for
// a namespaced template instantiation of the form
//   `n::tag-X<args>`
// the strip was skipped and the substring match against deferred
// entries like `n::X<args>::method(this)` failed.  As a result,
// constexpr methods of namespaced class templates remained in
// `deferred_typechecking` and were never drained, so
// `eligible_constexpr` in `typecheck_side_effect_function_call`
// stayed false, the conversion-operator call wasn't folded at
// template-arg-evaluation time, and using such a value as a
// non-type template argument failed with
//   expected constant expression, but got
//   'operator(bool)((const struct integral_constant *)&...)'

namespace n {

template <bool _v>
struct integral_constant
{
  static constexpr bool value = _v;
  using value_type = bool;
  using type = integral_constant<_v>;
  constexpr operator value_type() const noexcept { return value; }
};

using true_type = integral_constant<true>;
using false_type = integral_constant<false>;

} // namespace n

template <bool B>
struct gate
{
  static constexpr bool value = B;
};

// The crucial line: convert a value-initialised namespaced
// template-class temporary to bool at compile time, used as a
// non-type template argument.  Requires the strip-tag fix to
// drain `n::integral_constant<true>::operator(bool)` from
// `deferred_typechecking` so its body becomes available for
// constexpr evaluation.
using G = gate<n::true_type{}>;

int main()
{
  __CPROVER_assert(G::value, "namespaced constexpr operator bool resolved");
  return 0;
}
