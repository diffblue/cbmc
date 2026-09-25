// C++11 variadic sizeof
template <typename... Args>
int count()
{
  return sizeof...(Args);
}
int main()
{
  __CPROVER_assert(count<int, double, char>() == 3, "sizeof...");
  return 0;
}
