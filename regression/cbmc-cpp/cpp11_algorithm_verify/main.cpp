// Verify std::sort from <algorithm>
#include <algorithm>
#include <cassert>

int main()
{
  int a[] = {3, 1, 2};
  std::sort(a, a + 3);
  assert(a[0] == 1);
  assert(a[1] == 2);
  assert(a[2] == 3);
  return 0;
}
