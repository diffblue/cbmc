// Compile-only guard for regression/cbmc-cpp/cpp11_regex_match: full
// verification is beyond current BMC scaling (<regex> automaton state
// space), but the FRONT END must keep converting this cleanly.
#include <regex>

int main()
{
  std::regex r("hello");
  return std::regex_match("hello", r) ? 0 : 1;
}
