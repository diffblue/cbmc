#include <cassert>
#include <valarray>
int main()
{
  std::valarray<int> v(3);
  v[0] = 1;
  v[1] = 2;
  v[2] = 3;
  assert(v.sum() == 6);
  return 0;
}
