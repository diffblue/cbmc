#include <cassert>
int global = 0;
void take(int &&x)
{
  global = x;
}
int main()
{
  int a = 42;
  take(static_cast<int &&>(a));
  assert(global == 42);
  return 0;
}
