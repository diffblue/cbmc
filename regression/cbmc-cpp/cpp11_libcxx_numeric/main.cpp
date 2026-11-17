// libc++ std::accumulate
#include <numeric>
int main()
{
  int a[] = {1, 2, 3, 4};
  int sum = std::accumulate(a, a + 4, 0);
  __CPROVER_assert(sum == 10, "sum");
}
