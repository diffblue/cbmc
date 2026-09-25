// [temp.variadic]/5 + [expr.const]: a constexpr member function template of a
// class template instantiation may, in its body, expand the *enclosing class*
// parameter pack and its *own* parameter pack simultaneously in one pack
// expansion (a "zipped" expansion), e.g. `And<ctible<Ts, Us>...>::value`.
// This is the shape of libstdc++'s tuple constructor constraints
// (`__and_<is_constructible<_Types, _UTypes>...>::value`).
//
// CBMC type-checked such a constexpr member function template body with only
// the member's own pack bound -- the enclosing class's pack was not in the
// active template map -- so the zipped expansion was left unexpanded and the
// constexpr call could not be folded ("expected constant expression, but got
// 'ok()'").  The class template arguments are now brought into the active
// template map when the constexpr member function template definition is
// instantiated, so both packs resolve.

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
    return And<ge<Ts, Us>...>::value;
  }
};

template <bool C>
struct Sel
{
  static const int v = C ? 7 : 0;
};

int main()
{
  // ge<long,int> = sizeof(long) >= sizeof(int) = true; And<true> = true.
  __CPROVER_assert(
    Sel<Constraints<long>::ok<int>()>::v == 7,
    "zipped two-pack expansion folds");
  // ge<int,long> = sizeof(int) >= sizeof(long) = false; And<false> = false.
  __CPROVER_assert(
    Sel<Constraints<int>::ok<long>()>::v == 0,
    "zipped two-pack expansion folds (false)");
  // non-vacuity: a wrong value must FAIL.
  __CPROVER_assert(
    Sel<Constraints<long>::ok<int>()>::v == 0, "WRONG (must FAIL)");
  return 0;
}
