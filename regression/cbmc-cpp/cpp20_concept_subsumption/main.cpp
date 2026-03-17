#include <type_traits>

template <typename T>
concept Integral = std::is_integral_v<T>;

template <typename T>
concept SignedIntegral = Integral<T> && std::is_signed_v<T>;

template <Integral T>
int f(T)
{
  return 1;
}

template <SignedIntegral T>
int f(T)
{
  return 2;
}

int main()
{
  // SignedIntegral subsumes Integral, so f(42) should pick the more
  // constrained overload.
  __CPROVER_assert(f(42) == 2, "signed integral preferred");
}
