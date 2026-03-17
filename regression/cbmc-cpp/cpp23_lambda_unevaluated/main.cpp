// C++23 lambdas in unevaluated contexts
// Lambda in decltype creates a unique closure type
int main()
{
  auto f = [](int x) { return x; };
  using F = decltype(f);
  F g = f;
  int r = g(42);
  __CPROVER_assert(r == 42, "lambda in decltype");
  return 0;
}
