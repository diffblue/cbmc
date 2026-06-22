// [temp.variadic]/5 + [temp.deduct] + [expr.const]: a constexpr member function
// template body forms an outer template-id with MULTIPLE arguments, one of which
// is itself a template-id containing a pack expansion -- `And<bc<true>,
// And<ge<Ts, Us>...>>::value`, the shape of libstdc++'s
// `__and_<__constructible<U...>, __not_<__convertible<U...>>>::value`
// (std::tuple's constructor SFINAE).
//
// This used to fail to fold ("expected constant expression").  The root cause
// was NOT the nested pack expansion itself but the recursive variadic `And`:
// `And<B1, Bn...> : bc<B1::value && And<Bn...>::value>` recurses by peeling one
// element off `Bn` per level, and when this happened during a nested
// instantiation CBMC left the enclosing instance's `Bn` binding in the template
// map, so the recursive step inherited a stale pack and recursed onto itself.
// See cpp11_constexpr_recursive_variadic_and for the minimal, header-free
// reproduction.  Fixed by clearing a pack's recorded arguments when deduction
// resets the parameters (build_unassigned) and when a pack binds to zero
// elements during instantiation.

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
  // ge<long,int> = sizeof(long) >= sizeof(int) = true; And<true> = true;
  // And<bc<true>, And<true>> = true.
  __CPROVER_assert(
    Sel<Constraints<long>::ok<int>()>::v == 7,
    "nested pack expansion in multi-arg template-id folds (true)");
  // ge<int,long> = sizeof(int) >= sizeof(long) = false; And<false> = false;
  // And<bc<true>, And<false>> = false.
  __CPROVER_assert(
    Sel<Constraints<int>::ok<long>()>::v == 0,
    "nested pack expansion in multi-arg template-id folds (false)");
  // non-vacuity: a wrong value must FAIL.
  __CPROVER_assert(
    Sel<Constraints<long>::ok<int>()>::v == 0, "WRONG (must FAIL)");
  return 0;
}
