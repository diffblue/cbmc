// [expr.prim.lambda]/3-7: a lambda expression has a unique closure *class*
// type with a public inline `operator()` (the body) and, for a captureless
// lambda, a non-explicit conversion to a pointer-to-function.  The closure is
// an object, not a function pointer, so it can be stored by value in a
// type-erasing wrapper such as std::function.
//
// KNOWNBUG: CBMC models a captureless lambda as a bare function pointer, so a
// std::function constructed from a lambda stores a function pointer rather than
// a closure object and the type-erased call dereferences a null pointer.
// Reclassify CORE once a lambda is a closure object that std::function stores.
#include <functional>

int main()
{
  std::function<int(int)> f = [](int x) { return x + 1; };
  __CPROVER_assert(f(4) == 5, "std::function holds a lambda closure and calls it");
  return 0;
}
