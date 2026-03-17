#include <cassert>

int main()
{
  int x = 42;
  decltype(x) y = 10;
  assert(y == 10);
  return 0;
}
