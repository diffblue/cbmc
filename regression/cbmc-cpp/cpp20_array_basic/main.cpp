// C++20 std::array (works in C++17 but fails in C++20)
#include <array>
int main()
{
  std::array<int, 3> a = {1, 2, 3};
  __CPROVER_assert(a[1] == 2, "array element");
}
