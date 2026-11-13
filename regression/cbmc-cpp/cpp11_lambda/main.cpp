#include <cassert>
int main()
{
  int x = 10;
  auto f = [x](int y) { return x + y; };
  assert(f(5) == 15);
  return 0;
}
