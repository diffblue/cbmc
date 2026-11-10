// C++11 sizeof...(pack)
template <typename... Args>
int count(Args... args)
{
  return sizeof...(Args);
}
int main()
{
  int r = count(1, 2, 3);
  __CPROVER_assert(r == 3, "sizeof... pack");
  return 0;
}
