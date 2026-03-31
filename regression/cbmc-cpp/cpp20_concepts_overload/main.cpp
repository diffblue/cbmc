#if !defined(_MSC_VER) && __has_include(<concepts>)
// C++20 concept-constrained overload resolution
#  include <concepts>
template <typename T>
requires std::integral<T> T add(T a, T b)
{
  return a + b;
}
template <typename T>
requires std::floating_point<T> T add(T a, T b)
{
  return a + b;
}
int main()
{
  __CPROVER_assert(add(1, 2) == 3, "integral add");
  __CPROVER_assert(add(1.0, 2.0) == 3.0, "floating add");
}

#else
int main()
{
}
#endif
