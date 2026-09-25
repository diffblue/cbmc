// C++17 std::apply
#include <tuple>
int add(int a, int b)
{
  return a + b;
}
int main()
{
  auto t = std::make_tuple(1, 2);
  int r = std::apply(add, t);
  __CPROVER_assert(r == 3, "apply");
}
