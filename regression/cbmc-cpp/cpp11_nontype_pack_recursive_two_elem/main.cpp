// N5008 [temp.class.spec.match] + [temp.variadic]: a recursive class template
// over a NON-type parameter pack, selected via its `<H, Rest...>` partial
// specialization, must fold at every arity.
//
// KNOWNBUG: `sum_t<a, b>::v` for a recursive NON-type pack template fails to
// type-check ("could not fully type-check ... unsupported construct") for
// EXACTLY TWO elements, while 0, 1, 3, and 4 elements all fold correctly:
//
//   template<int...> struct sum_t;
//   template<> struct sum_t<> { static constexpr int v = 0; };
//   template<int H, int... T> struct sum_t<H, T...>
//     { static constexpr int v = H + sum_t<T...>::v; };
//   sum_t<2, 3>::v            // <-- fails (0/1/3/4-element sums are fine)
//
// The non-recursive partial-spec deduction alone (`sizeof...(Rest)` for
// `sum_t<H, Rest...>`) is correct at every arity, and the TYPE-pack analogue is
// fine, so the defect is specific to the RECURSIVE non-type-pack fold at the
// two-element level (the `sum_t<T...>` step forwarding a one-element non-type
// pack).  g++/clang++ compute sum_t<2,3>::v == 5.
//
// This is a residual non-type-pack defect surfaced while reproducing the
// (now-fixed, cpp11_alias_template_parallel_pack) tuple _TupleConstraints shape
// with a non-type `sum_t` proxy; the tuple itself uses TYPE packs and is not
// affected.  Flip to CORE once a recursive non-type-pack fold is correct at two
// elements.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands.

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
  __CPROVER_assert(sum_t<2, 3>::v == 5, "recursive non-type pack, 2 elements");
  __CPROVER_assert(sum_t<2, 3>::v != 5, "WRONG must FAIL");
  return 0;
}
