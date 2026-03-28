#if __has_include(<concepts>)
// C++20 shorthand concept constraint: template<std::integral T>
#  include <concepts>
template <std::integral T>
T f(T x)
{
  return x;
}
int main()
{
  __CPROVER_assert(f(1) == 1, "ok");
}

#else
int main()
{
}
#endif
