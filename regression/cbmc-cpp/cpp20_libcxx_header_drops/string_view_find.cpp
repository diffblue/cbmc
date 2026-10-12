#include <string_view>

extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string_view s = "hello";
  __CPROVER_assert(s.find(0x6c) == 2, "find");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
