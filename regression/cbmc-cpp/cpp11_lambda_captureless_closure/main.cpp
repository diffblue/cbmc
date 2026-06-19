// [expr.prim.lambda.closure]/1 + §7.5.6.2: a captureless, non-generic lambda
// has a closure *class* type with a public inline operator() and a non-explicit
// conversion to pointer-to-function with the same signature.  The lambda is
// thus usable both as an object (called via operator(), stored by value,
// deduced as the closure type) and as a function pointer (via the conversion).

template <typename F>
int apply_by_value(F f, int x)
{
  return f(x);
}

int main()
{
  auto lam = [](int x) { return x + 1; };

  // called as an object via operator()
  __CPROVER_assert(lam(4) == 5, "closure object operator() call");

  // deduced as the closure type and passed/stored by value
  __CPROVER_assert(apply_by_value(lam, 4) == 5, "closure passed by value to template");

  // copied as an object
  auto lam2 = lam;
  __CPROVER_assert(lam2(7) == 8, "closure copy then call");

  // converted to a function pointer (captureless lambda)
  int (*fp)(int) = lam;
  __CPROVER_assert(fp(9) == 10, "closure converts to function pointer");

  return 0;
}
