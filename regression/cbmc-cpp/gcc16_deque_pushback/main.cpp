// GCC 16's <deque> implementation causes VERIFICATION FAILED
// where VERIFICATION SUCCESSFUL is expected.
#include <cassert>
#include <deque>
int main()
{
  std::deque<int> d;
  d.push_back(1);
  assert(d.size() == 1);
}
