// C++14 decltype(auto) returning reference
int x = 42;
decltype(auto) get_ref()
{
  return (x);
}
int main()
{
  get_ref() = 10;
  __CPROVER_assert(x == 10, "decltype(auto) ref");
  return 0;
}
