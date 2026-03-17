#include <cassert>
#include <set>
int main()
{
  std::set<int> s;
  s.insert(42);
  s.insert(17);
  assert(s.size() == 2);
  assert(s.count(42) == 1);
  return 0;
}
