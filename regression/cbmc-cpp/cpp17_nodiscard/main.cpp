// C++17 [[nodiscard]]
[[nodiscard]] int compute()
{
  return 42;
}
int main()
{
  int r = compute();
  __CPROVER_assert(r == 42, "nodiscard");
  return 0;
}
