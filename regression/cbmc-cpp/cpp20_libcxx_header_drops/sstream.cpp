#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::ostringstream o;
  __CPROVER_assert(o.good(), "constructed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
