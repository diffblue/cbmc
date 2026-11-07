template <typename... Args>
int count()
{
  return sizeof...(Args);
}
int main()
{
  int a = count<int, double, char>();
  __CPROVER_assert(a == 3, "variadic count is 3");
  int b = count<>();
  __CPROVER_assert(b == 0, "empty pack count is 0");
  return 0;
}
