#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::ostringstream os;
  os << 7;
  __CPROVER_assert(os.str().size() == 1, "one digit");
  __CPROVER_assert(os.str().size() == 0, "WRONG (must FAIL)");
  return 0;
}
