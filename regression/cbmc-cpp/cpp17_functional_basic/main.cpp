#include <functional>
int add(int a, int b)
{
  return a + b;
}
int main()
{
  std::function<int(int, int)> f = add;
  return 0;
}
