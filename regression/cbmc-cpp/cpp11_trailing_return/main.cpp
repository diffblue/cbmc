// C++11 trailing return type
auto add(int a, int b) -> int
{
  return a + b;
}
int main()
{
  int r = add(3, 4);
  __CPROVER_assert(r == 7, "trailing return");
  return 0;
}
