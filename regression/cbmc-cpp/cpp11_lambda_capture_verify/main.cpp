// C++11 lambda capture by value and reference
int main()
{
  int x = 10;
  int y = 20;
  auto f = [x, &y]() { y = x + 1; };
  f();
  __CPROVER_assert(x == 10, "captured by value");
  __CPROVER_assert(y == 11, "captured by ref");
  return 0;
}
