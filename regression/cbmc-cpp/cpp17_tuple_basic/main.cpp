#include <cassert>
#include <tuple>
int main()
{
  std::tuple<int, int> t(1, 2);
  assert(std::get<0>(t) == 1);
  return 0;
}
