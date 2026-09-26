#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  bool t = true, f = false;
  auto r = t <=> true;
  __CPROVER_assert(r == 0, "bool <=> bool equal");
  auto r2 = f <=> true;
  __CPROVER_assert(r2 < 0, "false < true");
  std::strong_ordering s = (f == f) <=> true;
  __CPROVER_assert(s == 0, "comparison result <=> true");
  __CPROVER_assert(r2 == 0, "WRONG (must FAIL)");
}
