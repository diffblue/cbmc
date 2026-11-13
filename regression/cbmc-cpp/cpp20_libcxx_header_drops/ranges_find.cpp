#include <algorithm>
#include <ranges>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[] = {3, 1, 2};
  __CPROVER_assert(*std::ranges::find(a, 1) == 1, "find");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
