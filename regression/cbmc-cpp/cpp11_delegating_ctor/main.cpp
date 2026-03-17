#include <cassert>
struct S
{
  int x, y;
  S(int a) : x(a), y(0)
  {
  }
  S(int a, int b) : S(a)
  {
    y = b;
  }
};
int main()
{
  S s(1, 2);
  assert(s.x == 1 && s.y == 2);
  return 0;
}
