// libc++-20 basic vector test
#include <vector>
#include <cassert>
int main()
{
  std::vector<int> v;
  v.push_back(42);
  assert(v[0] == 42);
  return 0;
}
