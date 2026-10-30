// std::string::find(char) lowers to char_traits<char>::find, which
// calls __builtin_memchr.  CBMC had NO model for memchr: the call was
// havocked, so find returned a nondeterministic index and the pointer
// subtraction `__p - __data` inside basic_string::find tripped every
// pointer check (provenance-less pointer).  Now modeled per C23
// 7.26.5.2 (src/ansi-c/library/string.c), preserving provenance by
// returning a pointer into the searched object.
// g++/clang++ accept and verify at runtime.
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::string s = "ab";
  __CPROVER_assert(s.find('b') == 1, "find locates the character");
  __CPROVER_assert(
    s.find('z') == std::string::npos, "absent character yields npos");
  return 0;
}
