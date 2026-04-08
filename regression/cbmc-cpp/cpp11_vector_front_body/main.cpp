#include <vector>
#include <cassert>
int main()
{
  std::vector<int> v;
  v.push_back(1);
  assert(v.front() == 1);
}
