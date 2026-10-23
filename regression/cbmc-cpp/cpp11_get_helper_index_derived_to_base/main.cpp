// N5008 [temp.deduct.call]/4.3 (same template family) + [temp.variadic]/7.
// `tailcount<__i>(TImpl<__i, Head, Tail...>&)` has an explicitly specified
// non-type index `__i`.  Called on a `TImpl<0, int, int>` argument, `__i = 1`
// does not match the argument's own first template argument (0), so the
// argument is not itself a specialization of the parameter type -- but it is
// DERIVED from one: its base subobject `TImpl<1, int>`.  Deduction must use
// that base, giving `Head = int` and an empty `Tail`, so `sizeof...(Tail)`
// is 0.  (This is the shape of libstdc++'s
// `__get_helper<__i>(_Tuple_impl<__i, _Head, _Tail...>&)`.)
//
// Two regressions are exercised:
//  - the same-template derived-to-base case was not recognized (the fixed
//    non-type index 1 vs the argument's 0 was ignored), so `tailcount<1>` was
//    never instantiated and returned a nondet value;
//  - the empty trailing `Tail`, deduced from the base `TImpl<1, int>` whose
//    recorded template arguments carry the empty_typet zero-length-pack
//    sentinel, was miscounted as a one-element pack `<void>`
//    (`sizeof...(Tail) == 1`).
// Both are now fixed in guess_template_args (cpp_typecheck_resolve.cpp).
//
// Assertion 1 SUCCEEDs (index 0 has a one-element tail); assertion 2 SUCCEEDs
// (index 1, reached via derived-to-base, has an empty tail); assertion 3 (a
// wrong value) FAILs, proving non-vacuity.

template <unsigned long, typename...>
struct TImpl;

template <unsigned long I>
struct TImpl<I>
{
};

template <unsigned long I, typename Head, typename... Tail>
struct TImpl<I, Head, Tail...> : TImpl<I + 1, Tail...>
{
};

template <unsigned long I, typename Head, typename... Tail>
int tailcount(TImpl<I, Head, Tail...> &)
{
  return (int)sizeof...(Tail);
}

// Resolved during the deferred method-body drain (the failing context); the
// `tailcount<1>(t)` call needs derived-to-base deduction to `TImpl<1, int>`.
int wrapper0(TImpl<0, int, int> &t)
{
  return tailcount<0>(t);
}
int wrapper1(TImpl<0, int, int> &t)
{
  return tailcount<1>(t);
}

int main()
{
  TImpl<0, int, int> t;
  __CPROVER_assert(wrapper0(t) == 1, "index 0 has a one-element tail");
  __CPROVER_assert(
    wrapper1(t) == 0, "index 1 (derived-to-base) has an empty tail");
  __CPROVER_assert(wrapper1(t) == 5, "WRONG (must FAIL)");
  return 0;
}
