// N5008 [locale.ctype.members]/1, [locale.ctype.virtuals]/7: ctype<char>::tolower
// returns do_tolower(c), the lower-case letter for an upper-case one in the
// "C" locale ([locale.general]/8)
#include <locale>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::locale loc;
  const std::ctype<char> &f = std::use_facet<std::ctype<char>>(loc);
  char c = f.tolower('A');
  __CPROVER_assert(c == 'a', "tolower");
  __CPROVER_assert(c == 'A', "WRONG (must FAIL)");
  return 0;
}
