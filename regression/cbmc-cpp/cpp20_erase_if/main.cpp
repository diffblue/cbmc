// C++20 std::erase_if
#include <vector>
int main()
{
  std::vector<int> v;
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  v.push_back(4);
  v.push_back(5);
  std::erase_if(v, [](int x) { return x % 2 == 0; });
  __CPROVER_assert(v.size() == 3, "erase_if");
}
