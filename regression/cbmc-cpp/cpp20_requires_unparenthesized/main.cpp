// C++20: requires clause without parentheses, including compound expressions
#include <cassert>

template <typename T>
concept Integral = requires
{
  T(0);
};

template <typename T>
concept Signed = requires(T a)
{
  -a;
};

template <typename T>
requires Integral<T> T identity(T a)
{
  return a;
}

template <typename T>
requires Integral<T> &&Signed<T> T negate(T a)
{
  return -a;
}

int main()
{
  int r1 = identity(42);
  int r2 = negate(42);
  assert(r1 == 42);
  assert(r2 == -42);
}
