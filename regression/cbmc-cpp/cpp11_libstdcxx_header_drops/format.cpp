#include <format>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string s = std::format("{}", 42);
  __CPROVER_assert(s == "42", "format");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
