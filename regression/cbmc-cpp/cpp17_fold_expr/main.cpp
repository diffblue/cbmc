// C++17 fold expressions
template <typename... Ts>
int sum(Ts... args)
{
  return (args + ...);
}

template <typename... Ts>
bool all(Ts... args)
{
  return (args && ...);
}

int main()
{
  int r = sum(1, 2, 3);
  __CPROVER_assert(r == 6, "sum fold");
  bool b = all(true, true, true);
  __CPROVER_assert(b, "all fold");
  return 0;
}
