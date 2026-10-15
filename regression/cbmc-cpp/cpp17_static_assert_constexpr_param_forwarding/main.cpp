// Issue 14: N5008 [dcl.pre]/10, [expr.const]: the static_assert condition
// f(1) == 2 is a constant expression -- f forwards its parameter e to the
// constexpr function p2.  Builds of this branch from September 2026
// (5186cc5fe7) rejected it ("symbol 'e' is unknown"); upstream cbmc-6.9.0
// fails to parse it.  The negative variant false.cpp checks that the
// condition is evaluated, not ignored.
extern "C" void __CPROVER_assert(bool, const char *);
#include <cstddef>
constexpr size_t p2(size_t x)
{
  return size_t(1) << x;
}
constexpr size_t f(size_t e)
{
  return p2(e);
}
static_assert(f(1) == 2);
static_assert(f(3) == 8, "deeper forwarding");
int main()
{
  size_t e = 2;
  __CPROVER_assert(f(e) == 4, "run-time call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
