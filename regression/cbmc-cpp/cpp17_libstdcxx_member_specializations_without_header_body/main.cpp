// libstdc++ declares explicit specializations for char of the member
// basic_istream<char>::ignore(streamsize) (<istream>) and of getline(
// basic_istream<char> &, basic_string<char> &, char) (bits/basic_string.h),
// defined only in libstdc++.so.  N5008 [istream.unformatted]/25 and
// [string.io]/6 specify them; uses now instantiate the primary templates'
// definitions.
extern "C" void __CPROVER_assert(bool, const char *);
#include <sstream>
#include <string>
int main()
{
  std::istringstream in("ab cd");
  in.ignore(3);
  std::string s;
  in >> s;
  __CPROVER_assert(s == "cd", "ignore then extract");
  std::istringstream lines("x;y");
  std::string first;
  std::getline(lines, first, ';');
  __CPROVER_assert(first == "x", "getline with delimiter");
  __CPROVER_assert(s == "ab", "WRONG (must FAIL)");
  return 0;
}
