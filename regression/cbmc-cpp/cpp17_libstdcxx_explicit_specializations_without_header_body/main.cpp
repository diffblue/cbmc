// libstdc++ declares explicit specializations for char of
//   operator>>(basic_istream<char> &, basic_string<char> &)
//   __copy_streambufs_eof(basic_streambuf<char> *, ...)  (`out << sb')
// (bits/basic_string.h, <streambuf>) and defines them only in libstdc++.so.
// The front end selects the declared specialization ([temp.expl.spec]),
// which has no body, so `in >> s' and `out << in.rdbuf()' leave their
// results nondeterministic and the correct assertions below fail.  A model
// (or the primary template's definition) is needed for these functions.
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
