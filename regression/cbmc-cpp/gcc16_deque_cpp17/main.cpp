// GCC 16's <deque> in C++17 mode causes wrong results.
#include <cassert>
#include <deque>
int main()
{
  std::deque<int> d;
  d.push_back(1);
  d.push_front(2);
  assert(d.size() == 2);
}
