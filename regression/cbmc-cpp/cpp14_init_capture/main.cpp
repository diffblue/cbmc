// C++14 init capture in lambda
int main()
{
  int x = 10;
  auto f = [y = x + 5]() { return y; };
  int r = f();
  __CPROVER_assert(r == 15, "init capture");
  return 0;
}
