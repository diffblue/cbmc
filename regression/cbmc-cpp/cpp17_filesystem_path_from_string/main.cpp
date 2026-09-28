#include <filesystem>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string name = "a.txt";
  std::filesystem::path p(name);
  __CPROVER_assert(!p.empty(), "path from a std::string is not empty");
  __CPROVER_assert(p.empty(), "WRONG (must FAIL)");
}
