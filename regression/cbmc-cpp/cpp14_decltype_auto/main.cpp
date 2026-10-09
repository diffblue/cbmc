// C++14 decltype(auto) return type (value case)
decltype(auto) get_val()
{
  return 42;
}
int main()
{
  int r = get_val();
  __CPROVER_assert(r == 42, "decltype(auto) value");
  return 0;
}
