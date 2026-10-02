#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // [basic.ios.cons] Table 128: the postconditions of basic_ios::init
  std::ostringstream o;
  __CPROVER_assert(o.rdbuf() != nullptr, "rdbuf");
  __CPROVER_assert(o.tie() == nullptr, "tie");
  __CPROVER_assert(o.rdstate() == std::ios_base::goodbit, "rdstate");
  __CPROVER_assert(o.exceptions() == std::ios_base::goodbit, "exceptions");
  __CPROVER_assert(
    o.flags() == (std::ios_base::skipws | std::ios_base::dec), "flags");
  __CPROVER_assert(o.width() == 0 && o.precision() == 6, "width precision");
  // [iostate.flags]: setstate
  o.setstate(std::ios_base::failbit);
  __CPROVER_assert(o.fail() && !o.bad() && !o.good(), "failbit");
  // [locale.cons]/7: a copy of the stream's locale
  std::locale l = o.getloc();
  std::locale m(l);
  (void)m;
  __CPROVER_assert(o.good(), "WRONG (must FAIL)");
}
