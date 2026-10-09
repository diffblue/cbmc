// N5008 [over.match.best], [over.ics.user]: calling std::stoll with a
// string LITERAL requires the user-defined conversion const char* ->
// std::string and must select the narrow-string overload; the wstring
// overload is simply not viable.  CBMC hard-errors converting the
// argument against the WIDE overload ("invalid implicit conversion
// from 'const char *' to 'const int *'") instead of discarding it.
// Same family: std::ofstream{std::string} picks a constructor
// expecting std::streamsize (goto_harness_parse_options.cpp).
// Found dog-fooding src/util/string2int.cpp callers.
// g++/clang++ accept and verify at runtime.
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  long long v = std::stoll("41", nullptr, 10);
  __CPROVER_assert(v == 41, "stoll on a string literal");
  return 0;
}
