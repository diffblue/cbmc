#include <cassert>

auto add(int a, int b) -> int
{
  return a + b;
}

int main()
{
  assert(add(3, 4) == 7);
  return 0;
}
