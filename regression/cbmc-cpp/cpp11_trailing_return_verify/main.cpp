// C++11 trailing return type
auto add(int a, int b) -> int
{
  return a + b;
}
int main()
{
  __CPROVER_assert(add(1, 2) == 3, "trailing return");
  return 0;
}
