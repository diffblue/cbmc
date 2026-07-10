// N5008 [temp.class.spec.match] + [temp.variadic]: a recursive class template
// over a NON-type parameter pack, selected via its `<H, T...>` partial
// specialization, folds at every arity.
//
//   template<int...> struct sum_t;
//   template<> struct sum_t<> { static constexpr int v = 0; };
//   template<int H, int... T> struct sum_t<H, T...>
//     { static constexpr int v = H + sum_t<T...>::v; };
//
// This previously failed for EXACTLY TWO elements (`sum_t<2,3>::v`): the nested
// `sum_t<3>` (trailing pack `T` deduces empty) had its specialization pattern
// `<H, T...>` re-type-checked with `T...` still present, and a non-type pack
// expansion over an empty pack was evaluated as an unassigned scalar and threw,
// so `sum_t<3>` fell back to the incomplete primary.  Now the empty deduced
// trailing pack is trimmed before the pattern re-type-check
// ([temp.arg.explicit]/4 note 1, [temp.variadic]/4).
//
// CORE (was KNOWNBUG cpp11_nontype_pack_recursive_two_elem).  Non-vacuous: the
// two-element assertion is exactly the one that used to fail.

extern "C" void __CPROVER_assert(int, const char *);

template <int...>
struct sum_t;
template <>
struct sum_t<>
{
  static constexpr int v = 0;
};
template <int H, int... T>
struct sum_t<H, T...>
{
  static constexpr int v = H + sum_t<T...>::v;
};

int main()
{
  __CPROVER_assert(sum_t<>::v == 0, "0 elements");
  __CPROVER_assert(sum_t<5>::v == 5, "1 element");
  __CPROVER_assert(sum_t<2, 3>::v == 5, "2 elements (regression point)");
  __CPROVER_assert(sum_t<9, 9>::v == 18, "2 elements, equal");
  __CPROVER_assert(sum_t<1, 2, 3>::v == 6, "3 elements");
  __CPROVER_assert(sum_t<1, 2, 3, 4>::v == 10, "4 elements");
  return 0;
}
