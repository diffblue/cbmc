template <typename... Args>
int count_types(Args... args)
{
  return sizeof...(Args);
}

template <typename... Args>
int count_args(Args... args)
{
  return sizeof...(args);
}

int main()
{
  int r1 = count_types(1, 2, 3);
  __CPROVER_assert(r1 == 3, "sizeof...(Types) == 3");
  int r2 = count_args(1, 2, 3);
  __CPROVER_assert(r2 == 3, "sizeof...(args) == 3");
  int r3 = count_args(42);
  __CPROVER_assert(r3 == 1, "sizeof...(args) == 1");
  return 0;
}
