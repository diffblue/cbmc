// libc++-20 C++20 vector test
#include <vector>
int main()
{
  std::vector<int> v;
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  __CPROVER_assert(v.size() == 3, "size");
  return 0;
}
