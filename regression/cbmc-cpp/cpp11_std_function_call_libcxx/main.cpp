#include <functional>
extern "C" void __CPROVER_assert(bool, const char *);
int one()
{
  return 1;
}
int main()
{
  std::function<int()> f = one;
  __CPROVER_assert(f() == 1, "call");
  __CPROVER_assert(f() == 0, "WRONG (must FAIL)");
  return 0;
}
