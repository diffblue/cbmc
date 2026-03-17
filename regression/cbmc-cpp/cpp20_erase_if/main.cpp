// C++20 std::erase_if
#include <vector>
int main()
{
  std::vector<int> v = {1, 2, 3, 4, 5};
  std::erase_if(v, [](int x) { return x % 2 == 0; });
  __CPROVER_assert(v.size() == 3, "erase_if");
}
