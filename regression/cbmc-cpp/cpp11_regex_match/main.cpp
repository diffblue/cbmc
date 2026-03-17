// std::regex_match operation
#include <regex>
int main()
{
  std::regex r("hello");
  __CPROVER_assert(std::regex_match("hello", r), "regex match");
}
