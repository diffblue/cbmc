// C++14 decltype(auto) returning reference via parenthesized expression
int x = 42;
decltype(auto) get_ref()
{
  return (x);
}

int main()
{
  decltype(auto) r = get_ref();
  r = 100;
  __CPROVER_assert(x == 100, "decltype(auto) ref modifies original");
  return 0;
}
