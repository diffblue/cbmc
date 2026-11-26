// N5008 [string.view]: std::string_view substr and comparison.
#include <string_view>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string_view s = "hello";
  __CPROVER_assert(s.substr(1, 2) == "el", "string_view substr");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
