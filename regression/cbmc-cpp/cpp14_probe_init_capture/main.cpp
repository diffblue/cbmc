// N5008 [expr.prim.lambda.capture]: init-capture by move.
#include <memory>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto p = std::make_unique<int>(5);
  auto f = [q = std::move(p)] { return *q; };
  __CPROVER_assert(f() == 5, "init-capture by move");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
