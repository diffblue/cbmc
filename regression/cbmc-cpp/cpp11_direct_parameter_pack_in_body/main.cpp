// N5008 [temp.deduct.call]/1 + [temp.variadic]/8: deducing the parameter pack
// `U` of `packsize(Base<0, U...>)` from an argument of type `Base<0, int, int>`
// gives `U = <int, int>` -- the number of elements of a pack is the number of
// arguments deduced for it -- so `sizeof...(U)` is 2 and the specialization is
// `packsize<int, int>`.  (This is the *direct* deduction case: the argument is
// a specialization of the same class template, not a derived class as in the
// [temp.deduct.call]/4.3 case.)
//
// Regression: when such a call appeared in a function body other than main's
// (so it was type-checked during the deferred method-body drain rather than
// constant-folded), build_template_args emitted a single placeholder for the
// type-internal pack and it was not expanded to the deduced arity, so the
// callee was instantiated as the 1-element `packsize<int>` (sizeof...(U) == 1)
// and the call was left unbindable, dropping the enclosing body (which then
// returned a nondet value).  The placeholder is now expanded to the full
// deduced arity while draining deferred bodies.
//
// Assertion 1 SUCCEEDs (the pack has 2 elements); assertion 2 (a wrong value)
// FAILs, proving the assertions are evaluated non-vacuously.

template <unsigned long, typename...>
struct Base
{
};

template <typename... U>
int packsize(Base<0, U...>)
{
  return (int)sizeof...(U);
}

// Resolved during the deferred method-body drain (the context the fix
// targets); in main the call would instead be constant-folded.
int wrapper(Base<0, int, int> b)
{
  return packsize(b);
}

int main()
{
  Base<0, int, int> b;
  int n = wrapper(b);
  __CPROVER_assert(n == 2, "directly-deduced type-internal pack has arity 2");
  __CPROVER_assert(n == 3, "WRONG (must FAIL)");
  return 0;
}
