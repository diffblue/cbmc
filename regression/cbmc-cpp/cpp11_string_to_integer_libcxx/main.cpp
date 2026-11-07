extern "C" void __CPROVER_assert(bool, const char *);
#include <string>
// N5008 [string.conversions]/1-3: stoi, stol, stoul, stoll and stoull call
// strtol, strtoul, strtoll or strtoull on str.c_str() and store the index
// of the first unconverted character in *idx.  libc++ defines them in its
// compiled library.
int main()
{
  std::size_t idx = 0;
  int i = std::stoi(std::string("-12"));
  long long ll = std::stoll(std::string("41xyz"), &idx);
  unsigned long ul = std::stoul(std::string("ff"), nullptr, 16);
  __CPROVER_assert(i == -12, "stoi");
  __CPROVER_assert(ll == 41 && idx == 2, "stoll with index");
  __CPROVER_assert(ul == 255, "stoul base 16");
  __CPROVER_assert(ll == 42, "WRONG (must FAIL)");
  return 0;
}
