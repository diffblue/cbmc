// libstdc++ declares explicit specializations for char of
//   operator>>(basic_istream<char> &, basic_string<char> &)
//   __copy_streambufs_eof(basic_streambuf<char> *, ...)  (`out << sb')
// (bits/basic_string.h, <streambuf>) and defines them only in libstdc++.so.
// Uses instantiate the primary templates' definitions in the headers,
// which implement the behaviour N5008 specifies ([string.io]/1).
extern "C" void __CPROVER_assert(bool, const char *);
#include <sstream>
#include <string>
int main()
{
  std::istringstream in("abc");
  std::string s;
  in >> s;
  __CPROVER_assert(s == "abc", "extract a string");
  std::istringstream in2("xyz");
  std::ostringstream out;
  out << in2.rdbuf();
  __CPROVER_assert(out.str() == "xyz", "copy a stream buffer");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
