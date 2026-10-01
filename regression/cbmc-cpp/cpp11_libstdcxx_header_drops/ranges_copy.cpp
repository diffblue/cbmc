#include <algorithm>
#include <array>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::array<int, 2> a{1, 2};
  int o[2];
  std::ranges::copy(a.begin(), a.end(), o);
  __CPROVER_assert(o[1] == 2, "ranges::copy");
  __CPROVER_assert(o[1] != 2, "WRONG (must FAIL)");
}
