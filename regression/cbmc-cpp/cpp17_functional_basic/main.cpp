// std::function in C++17 mode, multi-argument.
//
// KNOWNBUG: with the layer-1 partial-spec pack deduction fixed
// (cpp11_partial_spec_pack_after_fixed), multi-argument std::function
// construction now resolves the converting constructor (previously it failed
// with "found no match for symbol 'function'" and this test passed only
// VACUOUSLY).  The remaining gap is that the handler pointers _M_invoker /
// _M_manager are not wired up during multi-argument construction, so
// operator() dereferences a null _M_invoker.  Single-argument std::function
// invokes correctly and soundly, so this is specific to the
// _Function_handler<R(A...), F> pack shape.
//
// Non-vacuous: assertion.2 is deliberately wrong and MUST FAIL.  Flip to CORE
// once the multi-argument handler wiring is fixed.
#include <functional>

int add(int a, int b)
{
  return a + b;
}

int main()
{
  std::function<int(int, int)> f = add;
  int r = f(3, 4);
  __CPROVER_assert(r == 7, "multi-arg function call");
  __CPROVER_assert(r == 8, "WRONG must FAIL");
  return 0;
}
