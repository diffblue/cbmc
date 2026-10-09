#include <cassert>
#include <iterator>
int main()
{
  int arr[] = {1, 2, 3};
  auto b = std::begin(arr);
  auto e = std::end(arr);
  assert(std::distance(b, e) == 3);
  return 0;
}
