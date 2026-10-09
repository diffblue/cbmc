// <regex> crashes on GCC 9 (segfault during type-checking)
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
// std::regex_match operation
#  include <regex>
int main()
{
  std::regex r("hello");
  __CPROVER_assert(std::regex_match("hello", r), "regex match");
}

#else
int main()
{
}
#endif
