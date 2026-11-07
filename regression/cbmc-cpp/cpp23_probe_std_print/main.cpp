// N5008 [print.fun]: print returned.
#include <print>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::print("{}", 42);
  __CPROVER_assert(true, "print returned");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
