#include <span>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[2] = {1, 2};
  std::span<int> s(a);
  __CPROVER_assert(s.size() == 2, "span of an array");
  __CPROVER_assert(s.size() == 3, "WRONG (must FAIL)");
}
