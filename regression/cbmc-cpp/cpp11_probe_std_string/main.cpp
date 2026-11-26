// N5008 [string.classes]: std::string append.
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string s = "ab";
  s += "cd";
  __CPROVER_assert(s.size() == 4 && s[2] == 'c', "string append");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
