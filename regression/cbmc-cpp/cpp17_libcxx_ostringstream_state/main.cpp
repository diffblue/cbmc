#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // [ostringstream.cons]/1, [basic.ios.members]: a newly constructed stream
  // has state goodbit
  std::ostringstream o;
  __CPROVER_assert(o.good(), "constructed stream is good");
  __CPROVER_assert(!o.good(), "WRONG (must FAIL)");
}
