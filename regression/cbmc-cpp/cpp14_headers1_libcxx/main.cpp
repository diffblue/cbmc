#include <algorithm>
#include <cassert>
#include <map>
#include <memory>
#include <type_traits>
#include <utility>
#include <vector>

auto add(int a, int b)
{
  return a + b;
}

int main()
{
  // auto return type deduction
  assert(add(1, 2) == 3);

  // decltype(auto)
  int x = 42;
  decltype(auto) y = x;
  assert(y == 42);

  // variable template
  static_assert(std::is_same<decltype(y), int>::value, "");

  return 0;
}
