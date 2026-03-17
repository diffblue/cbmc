// C++17 template<auto> non-type template parameter
template <auto V>
int get()
{
  return (int)V;
}

int main()
{
  int r = get<42>();
  __CPROVER_assert(r == 42, "template auto");
  return 0;
}
