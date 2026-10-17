// C++14 lambda init-capture
int main()
{
  int x = 10;
  auto f = [y = x + 1]() { return y; };
  int r = f();
  __CPROVER_assert(r == 11, "lambda init capture");
  return 0;
}
