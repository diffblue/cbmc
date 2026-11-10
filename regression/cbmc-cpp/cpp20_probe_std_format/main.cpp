// N5008 [format]: std::format of an int.
#include <format>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string s = std::format("{}", 42);
  __CPROVER_assert(s == "42", "format an int");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
