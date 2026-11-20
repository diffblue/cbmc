extern "C" void __CPROVER_assert(bool, const char *);
#include <string>
// N5008 [string.conversions]/7: to_string(val) returns format("{}", val),
// for an integer its decimal digits with a leading '-' if it is negative
// ([format.string.std]/21, Table 105).  libc++ defines these functions in
// its compiled library.
int main()
{
  std::string a = std::to_string(-307);
  std::string b = std::to_string(0u);
  std::string c = std::to_string(-9223372036854775807LL - 1);
  std::string d = std::to_string(18446744073709551615ULL);
  __CPROVER_assert(a == "-307", "int");
  __CPROVER_assert(b == "0", "unsigned zero");
  __CPROVER_assert(c == "-9223372036854775808", "long long minimum");
  __CPROVER_assert(d == "18446744073709551615", "unsigned long long maximum");
  __CPROVER_assert(a == "307", "WRONG (must FAIL)");
  return 0;
}
