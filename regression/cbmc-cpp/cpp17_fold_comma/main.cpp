// C++17 fold expression with comma operator
int total = 0;
template <typename... Args>
void sum_all(Args... args)
{
  ((total += args), ...);
}
int main()
{
  sum_all(1, 2, 3);
  __CPROVER_assert(total == 6, "comma fold sum");
  return 0;
}
