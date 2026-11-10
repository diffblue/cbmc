#include <ranges>

extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int m = 0;
  for(int x : std::views::iota(1, 4))
    m += x;
  __CPROVER_assert(m == 6, "iota");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
