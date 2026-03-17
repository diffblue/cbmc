// C++14 relaxed constexpr
constexpr int sum_to(int n)
{
  int result = 0;
  for(int i = 1; i <= n; ++i)
    result += i;
  return result;
}
int main()
{
  int r = sum_to(10);
  __CPROVER_assert(r == 55, "relaxed constexpr");
  return 0;
}
