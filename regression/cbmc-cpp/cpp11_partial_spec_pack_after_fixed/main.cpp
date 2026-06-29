// N5008 [temp.spec.partial.match], [temp.deduct.type], [temp.variadic]/5: when
// a class template partial specialization places a template parameter pack
// AFTER one or more fixed (non-deduced) template arguments --
//   template <bool, bool, class F, class... A> struct RI;       // primary
//   template <class F, class... A> struct RI<false, false, F, A...>;
// -- and it is selected via the partial-specialization disambiguation path
// (e.g. as a dependent base class of another template), the pack `A` must be
// deduced to ALL the trailing arguments, not collapsed to one.
//
// This is the shape of libstdc++'s `__result_of_impl<false, false, _Functor,
// _ArgTypes...>` (the base of `__invoke_result`), and was the blocker behind
// multi-argument std::function's `_Callable`/`__is_invocable_r` constraint
// failing to elaborate ("found no match for symbol 'function'").
//
// KNOWN BUG: the deduced pack was collapsed to a single element (the scalar
// convenience binding) when the specialization was selected via the
// disambiguation path, so `sizeof...(A)` came out as 1 for a two-element pack.
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once the
// disambiguation path expands the deduced pack into positional arguments.

extern "C" void __CPROVER_assert(int, const char *);

template <bool, bool, class F, class... A>
struct RI
{
  static const int n = -1;
};
template <class F, class... A>
struct RI<false, false, F, A...>
{
  static const int n = (int)sizeof...(A);
};

template <class F, class... A>
struct IR : RI<false, false, F, A...>
{
};

struct L2
{
};

int main()
{
  __CPROVER_assert(
    IR<L2 &, bool, bool>::n == 2, "deduced pack arity through partial-spec base");
  __CPROVER_assert(IR<L2 &, bool, bool>::n == 1, "WRONG must FAIL");
  return 0;
}
