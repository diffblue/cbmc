#include <ranges>

extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[] = {3, 1, 2};
  int m = 0;
  for(int x : a | std::views::transform([](int x) { return 2 * x; }))
    m += x;
  __CPROVER_assert(m == 12, "transform");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
