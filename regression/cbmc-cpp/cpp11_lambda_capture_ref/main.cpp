int main()
{
  int x = 10;
  int y = 20;
  auto f = [x, &y]() { y = x + 1; };
  f();
  __CPROVER_assert(x == 10, "x unchanged (by value)");
  __CPROVER_assert(y == 11, "y modified (by ref)");
  return 0;
}
