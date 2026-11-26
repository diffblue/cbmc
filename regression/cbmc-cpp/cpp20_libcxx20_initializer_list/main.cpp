// libc++-20 C++20 brace initialization with initializer_list
#include <vector>
int main()
{
  std::vector<int> v{1, 2, 3};
  __CPROVER_assert(v.size() == 3, "size");
  return 0;
}
