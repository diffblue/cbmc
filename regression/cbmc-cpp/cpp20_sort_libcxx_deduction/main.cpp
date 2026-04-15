// libc++ std::sort in C++20 mode fails during template instantiation.
// The sort algorithm's deep template chain (sort -> __sort_impl ->
// __sort_dispatch -> __partial_sort -> __partial_sort_impl) fails
// because __partial_sort_impl cannot be instantiated: the template
// argument deduction or lookup fails for the internal helper.
#include <algorithm>
int main()
{
  int a[] = {3, 1, 4};
  std::sort(a, a + 3);
  __CPROVER_assert(a[0] == 1, "sorted first");
  __CPROVER_assert(a[2] == 4, "sorted last");
}
