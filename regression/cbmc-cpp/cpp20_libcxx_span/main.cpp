// libc++ std::span
#include <span>
int main()
{
  int a[] = {1, 2, 3};
  std::span<int> s(a, 3);
  __CPROVER_assert(s.size() == 3, "size");
}
