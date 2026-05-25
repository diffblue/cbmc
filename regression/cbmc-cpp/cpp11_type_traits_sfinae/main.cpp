#include <cassert>
#include <type_traits>

template <typename T>
typename std::enable_if<std::is_integral<T>::value, T>::type double_it(T x)
{
  return x * 2;
}

int main()
{
  static_assert(std::is_integral<int>::value, "int is integral");
  static_assert(!std::is_integral<double>::value, "double is not integral");
  static_assert(std::is_same<int, int>::value, "int is int");

  assert(double_it(5) == 10);

  return 0;
}
