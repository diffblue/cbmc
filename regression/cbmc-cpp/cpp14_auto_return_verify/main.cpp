// C++14 return type deduction
auto add(int a, int b)
{
  return a + b;
}
int main()
{
  __CPROVER_assert(add(1, 2) == 3, "auto return");
  return 0;
}
