// C++26 pack indexing in expression context
template <typename... Ts>
auto first(Ts... ts)
{
  return ts...[0];
}
int main()
{
  __CPROVER_assert(first(42, 2, 3) == 42, "pack index");
}
