#include <cassert>

int x = 42;
decltype(auto) y = x;

int main()
{
  decltype(auto) z = y;
  assert(z == 42);
  return 0;
}
