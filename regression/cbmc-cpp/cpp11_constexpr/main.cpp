#include <cassert>

constexpr int square(int x)
{
  return x * x;
}
constexpr int N = square(5);

int main()
{
  assert(N == 25);
  constexpr int M = square(3);
  assert(M == 9);
  return 0;
}
