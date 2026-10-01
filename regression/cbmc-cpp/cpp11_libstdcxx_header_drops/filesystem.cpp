#include <filesystem>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::filesystem::path p{"a"};
  __CPROVER_assert(!p.empty(), "path");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
