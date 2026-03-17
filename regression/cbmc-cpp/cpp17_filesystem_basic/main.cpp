// C++17 std::filesystem basic usage
#include <filesystem>

int main()
{
  std::filesystem::path p("/tmp/test.txt");
  __CPROVER_assert(p.has_filename(), "has filename");
  return 0;
}
