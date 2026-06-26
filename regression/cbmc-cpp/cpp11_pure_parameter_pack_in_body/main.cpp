// N5008 [temp.variadic]/4,8: `U... args` is a function parameter pack whose
// number of elements is the number of arguments provided; `sizeof...(U)` is
// that count.  Instantiating `count_args<int, int>` therefore yields 2.
//
// Regression: when a call to such a variadic function template appeared in a
// function body other than main's -- so it was type-checked during the
// deferred method-body drain rather than constant-folded -- instantiating the
// callee with a parameter pack of two or more elements threw and the enclosing
// body was discarded (the call then returned a nondet value).  A multi-element
// type pack is intentionally bound only via pack_args_map / pack_size_map (not
// a scalar type_map entry, which would collapse pack expansions and
// sizeof...), so the scalar lookup of the pack parameter's pattern found no
// binding and threw.  The pattern now resolves to its first element's type
// (its representative) so instantiation proceeds; sizeof...(U) is still taken
// from pack_size_map.  A single- or zero-element pack already worked (the
// single-element convenience binding / no expansion).
//
// Assertion 1 SUCCEEDs (the pack has 2 elements); assertion 2 (a wrong value)
// FAILs, proving the assertions are evaluated non-vacuously.

template <typename... U>
int count_args(U...)
{
  return (int)sizeof...(U);
}

// Called from a non-main function body, resolved during the deferred
// method-body drain (the context the fix targets).
int wrapper(int a, int b)
{
  return count_args(a, b);
}

int main()
{
  int n = wrapper(3, 4);
  __CPROVER_assert(n == 2, "function parameter pack has two elements");
  __CPROVER_assert(n == 3, "WRONG (must FAIL)");
  return 0;
}
