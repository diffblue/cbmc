// C++11 constexpr function
constexpr int factorial(int n)
{
  return n <= 1 ? 1 : n * factorial(n - 1);
}
int main()
{
  int r = factorial(5);
  __CPROVER_assert(r == 120, "constexpr factorial");
  return 0;
}
