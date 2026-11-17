// libc++ std::array basic operations
#include <array>
int main()
{
  std::array<int, 3> a = {{1, 2, 3}};
  __CPROVER_assert(a.size() == 3, "size");
  __CPROVER_assert(a[0] == 1, "first");
  __CPROVER_assert(a[2] == 3, "last");
}
