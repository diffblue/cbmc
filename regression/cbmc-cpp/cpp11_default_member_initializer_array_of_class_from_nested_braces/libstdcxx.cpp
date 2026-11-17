#include <regex>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::regex r("a");
  __CPROVER_assert(true, "regex constructed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
