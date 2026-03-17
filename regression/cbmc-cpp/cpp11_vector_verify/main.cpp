// Verify std::vector<int> basic operations
#include <cassert>
#include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(42);
  assert(v.size() == 1);
  assert(v[0] == 42);
  return 0;
}
