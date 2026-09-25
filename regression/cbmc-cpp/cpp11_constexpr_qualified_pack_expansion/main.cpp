// [temp.variadic]/4-5: a pack expansion's pattern is expanded once per element
// of the packs it mentions, and the pattern may be a *qualified* type -- a
// reference, pointer, or cv-qualified type wrapping the pack -- not just a bare
// pack or a template-id.  std::tuple's constructors expand the element pack
// with such a pattern, e.g. `_TupleConstraints<C, _Elements...>::
// __is_explicitly_constructible<const _Elements&...>()`, where the explicit
// template argument `const _Elements&...` is a reference-to-const pattern.
//
// CBMC expanded a pack-expansion template argument only when its pattern was a
// bare `cpp_name`, and `template_mapt::apply` substituted template parameters
// through `pointer` types but not the front-end `frontend_pointer` form used
// for source-level pointers/references.  As a result a pattern such as
// `const Ts&...`, `Ts&...`, or `Ts*...` carrying two or more elements was left
// unexpanded (collapsing to a single element, or with the pack left
// unsubstituted), so a surrounding constexpr trait could not be folded.  A
// single-element pack happened to work via the single-element `type_map`
// convenience binding.
//
// Fixed by (a) gating the expansion on the argument being a (top-level) pack
// expansion -- the actual packs are found by walking the whole pattern -- and
// (b) substituting through `frontend_pointer` in `template_mapt::apply`.

template <bool V>
struct bc
{
  static constexpr bool value = V;
};
template <class...>
struct And : bc<true>
{
};
template <class B1, class... Bn>
struct And<B1, Bn...> : bc<B1::value && And<Bn...>::value>
{
};

// True only for the exact reference-to-const types, so the assertions verify
// both the expanded count AND that the cv-ref qualification is applied per
// element.
template <class T>
struct is_cref_intlong : bc<false>
{
};
template <>
struct is_cref_intlong<const int &> : bc<true>
{
};
template <>
struct is_cref_intlong<const long &> : bc<true>
{
};

template <bool C>
struct Sel
{
  static const int v = C ? 7 : 0;
};

template <class... Ts>
struct TC
{
  // reference-to-const pattern expansion of the class pack.
  static constexpr bool ok()
  {
    return And<is_cref_intlong<const Ts &>...>::value;
  }
};

int main()
{
  // const int& and const long& both match -> And<...> = true.
  __CPROVER_assert(
    Sel<TC<int, long>::ok()>::v == 7,
    "reference-qualified pack expansion folds true");
  // const char& does not match -> And<...> = false.
  __CPROVER_assert(
    Sel<TC<int, char>::ok()>::v == 0,
    "reference-qualified pack expansion folds false");
  // non-vacuity: a wrong value must FAIL.
  __CPROVER_assert(Sel<TC<int, long>::ok()>::v == 0, "WRONG (must FAIL)");
  return 0;
}
