// C++11: trailing return type with decltype referencing parameters
auto add(int a, int b) -> decltype(a + b)
{
  return a + b;
}

int main()
{
  auto r = add(1, 2);
  __CPROVER_assert(r == 3, "trailing decltype");
}
