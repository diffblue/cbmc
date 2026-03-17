// std::sort in C++20 mode
#include <algorithm>
int main()
{
  int a[] = {3, 1, 4};
  std::sort(a, a + 3);
  __CPROVER_assert(a[0] == 1, "sorted");
}
