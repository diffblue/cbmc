#include <cassert>

constexpr int factorial(int n)
{
  int result = 1;
  for(int i = 2; i <= n; ++i)
    result *= i;
  return result;
}

int main()
{
  assert(factorial(5) == 120);
  return 0;
}
