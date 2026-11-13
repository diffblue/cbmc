#include <ranges>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  int sum = 0;
  for(auto x : arr | std::views::take(3))
    sum += x;
  __CPROVER_assert(sum == 6, "ranges take");
  __CPROVER_assert(sum == 7, "WRONG (must FAIL)");
}
