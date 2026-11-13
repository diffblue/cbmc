// N5008 [range.filter]: iterating over std::views::filter.
#include <ranges>
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector<int> v{1, 2, 3, 4};
  int s = 0;
  for(int x : v | std::views::filter([](int x) { return x % 2 == 0; }))
    s += x;
  __CPROVER_assert(s == 6, "views::filter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
