#include <ranges>

extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[] = {3, 1, 2};
  int n = 0;
  for(int x : a | std::views::filter([](int x) { return x != 1; }))
    n += x;
  __CPROVER_assert(n == 5, "filter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
