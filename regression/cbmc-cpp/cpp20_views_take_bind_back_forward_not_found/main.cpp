#include <ranges>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto v = std::views::take(3);
  (void)v;
  int reached = 1;
  __CPROVER_assert(reached == 1, "views::take(3) converts");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
}
