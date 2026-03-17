// C++11 recursive template metaprogramming
template <int N>
struct Fib
{
  static constexpr int value = Fib<N - 1>::value + Fib<N - 2>::value;
};
template <>
struct Fib<0>
{
  static constexpr int value = 0;
};
template <>
struct Fib<1>
{
  static constexpr int value = 1;
};

int main()
{
  __CPROVER_assert(Fib<6>::value == 8, "fib(6)");
  return 0;
}
