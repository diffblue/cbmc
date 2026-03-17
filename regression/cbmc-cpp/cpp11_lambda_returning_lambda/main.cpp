// C++11 lambda returning a lambda
int main()
{
  auto f = [](int x) { return [x](int y) { return x + y; }; };
  auto g = f(10);
  __CPROVER_assert(g(5) == 15, "lambda returning lambda");
  return 0;
}
