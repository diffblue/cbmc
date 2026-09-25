// N5008 [dcl.fct]/8: a function's parameters are in scope in its
// trailing return type.  A lambda's `-> decltype(__s)` naming its own
// parameter failed "symbol '__s' is unknown" (cvise converged on this
// from a preprocessed libc++ <string> seed): the trailing type was
// typechecked before the parameters were registered, AND the closure
// class's operator() declaration carried the raw parse tree, which the
// class conversion re-typechecked without parameter scope.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto f = [](int __s) -> decltype(__s) { return __s + 1; };
  __CPROVER_assert(f(41) == 42, "lambda trailing decltype");
  return 0;
}
