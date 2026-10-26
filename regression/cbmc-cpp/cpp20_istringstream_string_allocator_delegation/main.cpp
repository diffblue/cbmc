// N5008 [istringstream.cons]: basic_istringstream(const basic_string &,
// const Allocator &) is, in libstdc++ and libc++, a delegating constructor
// ([class.base.init]/6) of a class with the virtual base basic_ios: its
// target must construct basic_ios and its ios_base ([class.base.init]/7,
// 13.1), whose precision() is 6 ([basic.ios.cons]/4, Table 140).
#include <memory>
#include <sstream>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::string text = "42";
  std::allocator<char> a;
  std::istringstream in{text, a};
  __CPROVER_assert(in.precision() == 6, "virtual base constructed");
  __CPROVER_assert(in.precision() == 7, "WRONG (must FAIL)");
  return 0;
}
