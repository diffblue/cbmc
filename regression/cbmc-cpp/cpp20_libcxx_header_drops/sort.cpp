#include <algorithm>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[3] = {3, 1, 2};
  std::sort(a, a + 3);
  __CPROVER_assert(a[0] == 1 && a[2] == 3, "sorted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
