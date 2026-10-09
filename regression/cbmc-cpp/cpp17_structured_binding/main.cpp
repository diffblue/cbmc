#include <cassert>

struct Point
{
  int x;
  int y;
};

int main()
{
  Point p{3, 4};
  auto [a, b] = p;
  assert(a == 3);
  assert(b == 4);
  return 0;
}
