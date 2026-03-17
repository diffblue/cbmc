#include <cassert>

int main()
{
  int *p = nullptr;
  assert(p == nullptr);
  int x = 42;
  p = &x;
  assert(*p == 42);
  return 0;
}
