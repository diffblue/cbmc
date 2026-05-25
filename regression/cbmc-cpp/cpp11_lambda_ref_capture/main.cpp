// C++11 lambda reference capture
int main()
{
  int x = 10;
  auto f = [&x]() { x = 20; };
  f();
  __CPROVER_assert(x == 20, "ref capture");
  return 0;
}
