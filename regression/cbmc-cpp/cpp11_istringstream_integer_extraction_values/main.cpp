// N5008 [istream.formatted.arithmetic]/1-3, [facet.num.get.virtuals]/3:
// `s >> i' skips white space, converts the longest sequence of characters
// that forms an integer, and sets failbit (storing 0) when there is none.
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::istringstream s("42 -7 x");
  int a = 0, b = 0, c = 5;
  s >> a;
  __CPROVER_assert(!s.fail() && a == 42, "42");
  s >> b;
  __CPROVER_assert(!s.fail() && b == -7, "-7");
  s >> c;
  __CPROVER_assert(s.fail() && c == 0, "x is no integer");
  __CPROVER_assert(!s.fail(), "WRONG (must FAIL)");
  return 0;
}
