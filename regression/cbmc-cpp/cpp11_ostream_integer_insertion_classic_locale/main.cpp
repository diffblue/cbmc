// N5008 [ostream.inserters.arithmetic]/1, [facet.num.put.virtuals]: integer
// insertion formats through the num_put and numpunct facets of the stream's
// locale, here the "C" locale ([locale.general]/8): no grouping, decimal
// digits, the fill character applied for the field width.
#include <iomanip>
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::ostringstream o;
  o << -42;
  std::string s = o.str();
  __CPROVER_assert(
    s.size() == 3 && s[0] == '-' && s[1] == '4' && s[2] == '2',
    "negative decimal");

  std::ostringstream w;
  w << std::setw(3) << 7;
  std::string t = w.str();
  __CPROVER_assert(
    t.size() == 3 && t[0] == ' ' && t[1] == ' ' && t[2] == '7',
    "padded to the field width");

  __CPROVER_assert(s[1] == '2', "WRONG (must FAIL)");
  return 0;
}
