#include <cassert>

auto add(int a, int b)
{
  return a + b;
}

auto identity(int x)
{
  return x;
}

int main()
{
  assert(add(1, 2) == 3);
  assert(identity(42) == 42);
  return 0;
}
