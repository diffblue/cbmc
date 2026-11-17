// C++20 constrained auto
template <typename T>
concept Integral = __is_integral(T);

int main()
{
  Integral auto x = 42;
  __CPROVER_assert(x == 42, "constrained auto");
  return 0;
}
