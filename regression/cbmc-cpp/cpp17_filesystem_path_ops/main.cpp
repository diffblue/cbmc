// std::filesystem::path operations
#include <filesystem>
int main()
{
  std::filesystem::path p("/tmp/test.txt");
  __CPROVER_assert(p.has_filename(), "has filename");
}
