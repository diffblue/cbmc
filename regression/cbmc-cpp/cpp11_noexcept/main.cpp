#include <cassert>

int safe_add(int a, int b) noexcept
{
  return a + b;
}

int main()
{
  assert(safe_add(2, 3) == 5);
  return 0;
}
