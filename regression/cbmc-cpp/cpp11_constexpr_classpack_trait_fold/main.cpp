// [temp.variadic]/4-5 + [expr.const]: a constexpr function whose body expands a
// *class* parameter pack into a trait, e.g. `__and_<is_default_constructible<
// _Types>...>::value`, must fold.  This is the shape of std::tuple's
// constructor SFINAE: `_TupleConstraints<_Cond, _Types...>::
// __is_explicitly_default_constructible()` returns
//
//   __and_<is_default_constructible<_Types>...,
//          __not_<__and_<__is_implicitly_default_constructible<_Types>...>>
//         >::value
//
// and `__is_explicitly_constructible<_UTypes...>()` the analogous form.
//
// CBMC type-checked a pack-expansion template argument only when it arrived
// tagged `ambiguous`; an argument already resolved to a `type` carrying a
// multi-element class pack (e.g. `is_default_constructible<_Types>...` with two
// or more `_Types`) fell through unexpanded, collapsing the pack to a single
// element and leaving the trait unresolved -- so the constexpr call could not
// be folded ("expected constant expression").  Single-element packs happened to
// work via the single-element `type_map` convenience binding, so only tuples of
// two or more elements were affected.  The expansion now handles both `type`
// and `ambiguous` pack-expansion arguments ([temp.variadic]/4-5: the pattern is
// expanded once per pack element regardless of how the argument is tagged).

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
template <class B>
struct Not : bc<!B::value>
{
};
template <class A>
struct big : bc<(sizeof(A) >= 4)>
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
  // __is_..._default_constructible shape: __and_<trait<Ts>...>::value.
  static constexpr bool all_big()
  {
    return And<big<Ts>...>::value;
  }
  // __is_explicitly_constructible shape: a multi-argument __and_ whose second
  // argument is a nested __not_<__and_<trait<Ts>...>>.
  static constexpr bool not_all_small()
  {
    return And<big<Ts>..., Not<And<Not<big<Ts>>...>>>::value;
  }
};

int main()
{
  // big<int> = big<long> = true (sizeof >= 4) -> And<...> = true.
  __CPROVER_assert(
    Sel<TC<int, long>::all_big()>::v == 7, "class-pack trait folds true");
  // big<char> = false (sizeof 1) -> And<...> = false.
  __CPROVER_assert(
    Sel<TC<int, char>::all_big()>::v == 0, "class-pack trait folds false");
  // the std::tuple explicit-constructible shape (multi-arg + nested not/and).
  __CPROVER_assert(
    Sel<TC<int, long>::not_all_small()>::v == 7,
    "explicit-constructible shape folds true");
  // non-vacuity: a wrong value must FAIL.
  __CPROVER_assert(Sel<TC<int, long>::all_big()>::v == 0, "WRONG (must FAIL)");
  return 0;
}
