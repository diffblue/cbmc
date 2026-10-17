#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string s("loop");
  __CPROVER_assert(s == "loop", "compare");
  __CPROVER_assert(s.size() == 3, "WRONG (must FAIL)");
  return 0;
}
