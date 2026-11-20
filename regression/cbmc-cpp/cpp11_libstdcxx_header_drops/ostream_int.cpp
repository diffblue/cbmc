#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::ostringstream o;
  o << 4;
  __CPROVER_assert(o.str().size() == 1, "int inserted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
