#include <string>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string a("abc");
  std::string b(std::move(a));
  __CPROVER_assert(b.size() == 3, "moved string keeps its contents");
  __CPROVER_assert(b[1] == 'b', "element");
  __CPROVER_assert(b.size() == 4, "WRONG (must FAIL)");
}
