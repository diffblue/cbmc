extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [expr.prim.fold] + [dcl.fct]/8: a fold-expression over the
// function's own parameter pack in a trailing-return-type decltype.
// A single-element instantiation ([temp.variadic]/5) keeps the sole
// element's plain parameter name, so the fold reduces to that
// parameter and the declaration type-checks.
template <class... _Args>
auto sum(_Args... __x) -> decltype((__x + ... + 0))
{
  return (__x + ... + 0);
}

int main()
{
  __CPROVER_assert(sum(5) == 5, "single-element fold in trailing decltype");
  return 0;
}
