// N5008 [ostream.inserters.arithmetic]/1, [std.manip]/7: `ss << setw(4)
// << 7' formats 7 through the num_put facet of the stream's locale, padded
// to the field width.  This test is about the MSVC STL;
// cpp11_stream_setw and cpp11_ostream_integer_insertion_classic_locale
// cover libstdc++.
#ifndef _MSC_VER
#  error "this test needs the MSVC STL"
#endif
#include <iomanip>
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::stringstream ss;
  ss << std::setw(4) << 7;
  __CPROVER_assert(ss.str() == "   7", "padded to the field width");
  __CPROVER_assert(ss.str() == "7", "WRONG (must FAIL)");
  return 0;
}
