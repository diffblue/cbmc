// C++11 std::string basic usage
#include <string>

int main()
{
  std::string s = "hello";
  __CPROVER_assert(s.size() == 5, "string size");
  return 0;
}
