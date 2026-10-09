// C++20 concepts
template <typename T>
concept Integral = __is_same(T, int) || __is_same(T, long);

template <Integral T>
T add(T a, T b)
{
  return a + b;
}

int main()
{
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "1+2==3");
  return 0;
}
