// [temp.deduct]/[temp.variadic]: a variadic class template partial
// specialization whose base-class non-type argument names the SAME template
// with its own parameter pack -- the shape of libstdc++'s `__and_`:
//
//   template <class B1, class... Bn>
//   struct And<B1, Bn...> : bc<B1::value && And<Bn...>::value> {};
//
// recurses by peeling one element off the pack per level.  When such a trait
// was instantiated with two or more arguments inside a function body (so the
// instantiation is nested and an enclosing `And<...>` is mid-instantiation),
// CBMC left the enclosing instance's pack binding (`Bn = [X]`) in the template
// map while DEDUCING and BUILDING the recursive `And<Bn...>` step.  The inner
// step, whose own `Bn` is empty, therefore inherited the stale `Bn = [X]` and
// `And<Bn...>` re-expanded to the enclosing instance, recursing onto itself;
// the member `::value` could not be resolved and the constexpr call failed to
// fold ("expected constant expression").  Top-level uses (and single-argument
// uses, whose recursion bottoms out at the primary template) were unaffected,
// which is why only the >= 2-argument case -- the common one, and the shape of
// `std::tuple`'s constructor SFINAE -- was broken.
//
// The fix clears a parameter pack's recorded arguments when (a) deduction
// resets the parameters (`build_unassigned`) and (b) the pack binds to zero
// elements during instantiation, so the recursive step deduces an empty pack
// as required by [temp.deduct]/[temp.variadic].

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

template <bool C>
struct Sel
{
  static const int v = C ? 7 : 0;
};

// constexpr functions whose bodies instantiate a two-argument recursive And.
static constexpr bool all_true()
{
  return And<bc<true>, bc<true>>::value;
}
static constexpr bool has_false()
{
  return And<bc<true>, bc<false>>::value;
}

int main()
{
  __CPROVER_assert(Sel<all_true()>::v == 7, "And<true, true> folds to true");
  __CPROVER_assert(Sel<has_false()>::v == 0, "And<true, false> folds to false");
  // non-vacuity: a wrong value must FAIL.
  __CPROVER_assert(Sel<all_true()>::v == 0, "WRONG (must FAIL)");
  return 0;
}
