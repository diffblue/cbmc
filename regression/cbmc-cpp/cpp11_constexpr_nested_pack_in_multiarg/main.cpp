// [temp.variadic]/5 + [expr.const]: when a constexpr member function template
// body forms an outer template-id with MULTIPLE arguments, one of which is
// itself a template-id containing a pack expansion (e.g. `And<bc<true>,
// And<ge<Ts, Us>...>>::value`, or libstdc++'s
// `__and_<__constructible<U...>, __not_<__convertible<U...>>>::value`), CBMC
// does not expand the nested pack: the pack expansion is not at the top of the
// outer argument, so it is left unexpanded and the constexpr call cannot be
// folded ("expected constant expression, but got 'ok()'").
//
// KNOWNBUG: this is the remaining blocker for std::get on a std::tuple --
// libstdc++'s tuple constructor SFINAE (_TupleConstraints::
// __is_explicitly_constructible) nests pack-expanding template-ids inside a
// multi-argument __and_.  A single zipped expansion already folds (see
// cpp11_constexpr_zipped_pack_expansion); the nested case does not yet.
// Reclassify CORE once nested pack expansions in multi-argument template-ids
// are expanded.

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
template <class A, class B>
struct ge : bc<(sizeof(A) >= sizeof(B))>
{
};

template <class... Ts>
struct Constraints
{
  template <class... Us>
  static constexpr bool ok()
  {
    return And<bc<true>, And<ge<Ts, Us>...>>::value;
  }
};

template <bool C>
struct Sel
{
  static const int v = C ? 7 : 0;
};

int main()
{
  __CPROVER_assert(
    Sel<Constraints<long>::ok<int>()>::v == 7,
    "nested pack expansion in multi-arg template-id folds");
  return 0;
}
