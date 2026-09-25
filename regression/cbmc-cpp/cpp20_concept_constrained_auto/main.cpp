// C++20 constrained auto parameter
#include <type_traits>

template <typename T>
concept Integral = std::is_integral_v<T>;

int f(Integral auto x)
{
  return x * 2;
}

int main()
{
  __CPROVER_assert(f(21) == 42, "constrained auto");
}
