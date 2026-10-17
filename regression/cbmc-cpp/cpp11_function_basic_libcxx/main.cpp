// libc++ std::function basic usage
#include <functional>

int add(int a, int b)
{
  return a + b;
}

int main()
{
  std::function<int(int, int)> f = add;
  int r = f(3, 4);
  __CPROVER_assert(r == 7, "function call");
  return 0;
}
