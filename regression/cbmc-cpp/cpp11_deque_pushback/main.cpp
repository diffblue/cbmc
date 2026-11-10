#include <cassert>
#include <deque>
int main()
{
  std::deque<int> d;
  d.push_back(1);
  d.push_front(2);
  assert(d.size() == 2);
  return 0;
}
