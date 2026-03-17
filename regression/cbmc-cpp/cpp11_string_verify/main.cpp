// Verify std::string basic operations
#include <cassert>
#include <string>

int main()
{
  std::string s = "hello";
  assert(s.size() == 5);
  return 0;
}
