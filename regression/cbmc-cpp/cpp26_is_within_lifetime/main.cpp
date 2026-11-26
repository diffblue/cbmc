// N5008 [meta.const.eval]: within its lifetime.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
constexpr bool f()
{
  int x = 1;
  return std::is_within_lifetime(&x);
}
int main()
{
  __CPROVER_assert(f(), "within its lifetime");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
