// std::erase_if over a populated std::vector should remove the matching
// elements and shrink the container: erasing the single element equal to 2
// from {1, 2, 3} must leave size 2.
#include <vector>

int main()
{
  std::vector<int> v;
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  std::erase_if(v, [](int x) { return x == 2; });
  __CPROVER_assert(v.size() == 2, "size is 2 after erase_if removes one element");
  return 0;
}
