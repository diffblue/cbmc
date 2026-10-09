// C++11 std::array with aggregate initialization and __CPROVER_assert
#include <array>

int main()
{
  std::array<int, 3> a = {{1, 2, 3}};
  __CPROVER_assert(a[0] == 1, "array access");
  __CPROVER_assert(a.size() == 3, "array size");
  return 0;
}
