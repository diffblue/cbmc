// N5008 [temp.deduct.call]/4.3 + Example 5: when a function parameter is a
// class template-id `Base<..., U...>` and the call argument is of a class type
// derived from a specialization of `Base`, the template argument pack `U` is
// deduced from the base-class subobject of the argument (the deduced A is the
// base specialization).  Here `packsize(Base<0, U...>)` called with a
// `Der<int, int>` argument (whose base is `Base<0, int, int>`) deduces
// `U = <int, int>`, so `sizeof...(U) == 2`.
//
// Regression: when such a call appears in a function body other than main's
// (so it is type-checked during the deferred method-body drain rather than
// constant-folded), the type-internal pack `U` was instantiated with the
// wrong arity -- a 1-element `packsize<int>` (whose `sizeof...(U)` is 1), or
// the call was left unbindable and the enclosing body dropped (returning a
// nondet value).  build_template_args emits a single placeholder for a
// type-internal pack; for a derived-to-base-deduced pack that placeholder is
// now expanded to the full deduced arity in cpp_typecheck_resolve.cpp.
//
// Assertion 1 SUCCEEDs (the pack has 2 elements); assertion 2 (a wrong value)
// FAILs, proving the assertions are evaluated non-vacuously.

template <unsigned long, typename...>
struct Base
{
};

template <typename T1, typename T2>
struct Der : Base<0, T1, T2>
{
};

template <typename... U>
int packsize(Base<0, U...>)
{
  return (int)sizeof...(U);
}

// Resolved during the deferred method-body drain (not main), which is the
// context the fix targets; in main the call would be constant-folded.
int wrapper(Der<int, int> d)
{
  return packsize(d);
}

int main()
{
  Der<int, int> d;
  int n = wrapper(d);
  __CPROVER_assert(n == 2, "derived-to-base pack deduced with arity 2");
  __CPROVER_assert(n == 3, "WRONG (must FAIL)");
  return 0;
}
