// C++11 std::regex basic usage
#include <regex>

int main()
{
  std::regex r("hello");
  __CPROVER_assert(std::regex_match("hello", r), "match");
  return 0;
}
