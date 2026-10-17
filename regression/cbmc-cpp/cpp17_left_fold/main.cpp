// C++17 left fold expression
template <typename... Ts>
bool all(Ts... args)
{
  return (... && args);
}

int main()
{
  bool r = all(true, true);
  __CPROVER_assert(r, "left fold all true");
  return 0;
}
