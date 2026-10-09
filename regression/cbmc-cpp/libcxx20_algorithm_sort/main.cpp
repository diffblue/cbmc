// libc++-20's <algorithm> uses C++20 constructs in internal
// headers that CBMC's parser cannot handle.
#include <algorithm>
int main()
{
  int a[] = {3, 1, 2};
  std::sort(a, a + 3);
  __CPROVER_assert(a[0] == 1, "sorted");
}
