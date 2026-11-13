#include <functional>

// N5008 [func.wrap.func]: invoking a std::function bound to a lambda
// runs the lambda.  CBMC converts the construction and the call, but
// the invocation does not reach the closure: the by-reference
// parameter stays unconstrained (the assertion fails and the
// dereference checks fire on a null pointer).  The shape of
// with_solver_hardness(dp, [](solver_hardnesst &h) {...}) in
// src/goto-symex/solver_hardness.h, which blocks dog-fooding its
// callers (goto_symex_property_decider.cpp).
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

static void apply(std::function<void(int &)> handler)
{
  int v = 41;
  handler(v);
  __CPROVER_assert(v == 42, "handler ran through std::function");
}

int main()
{
  apply([](int &x) { x += 1; });
  return 0;
}
