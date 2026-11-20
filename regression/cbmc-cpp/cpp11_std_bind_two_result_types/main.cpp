extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
int add(int a, int b)
{
  return a + b;
}
int g_acc = 0;
void vadd(int b)
{
  g_acc += b;
}
int main()
{
  // A void-returning bind first: its result_of / __invoke_result chain must
  // not leak into the int-returning bind that follows.
  auto g = std::bind(vadd, 5);
  g();
  __CPROVER_assert(g_acc == 5, "first: void-returning bind");
  auto f = std::bind(add, 1, 10);
  __CPROVER_assert(f() == 11, "second: int-returning bind is not void");
  std::function<int(int)> h = std::bind(add, std::placeholders::_1, 10);
  __CPROVER_assert(h(4) == 14, "third: bind -> std::function after the others");
  return 0;
}
