#include <array>
#include <cassert>
int main()
{
  std::array<int, 3> a = {{1, 2, 3}};
  assert(a.size() == 3);
  assert(a[0] == 1);
  assert(a[2] == 3);
  return 0;
}
