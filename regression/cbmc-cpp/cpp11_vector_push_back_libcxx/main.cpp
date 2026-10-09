// C++11 std::vector push_back
#include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(42);
  __CPROVER_assert(v.size() == 1, "vector size");
  __CPROVER_assert(v[0] == 42, "vector element");
  return 0;
}
