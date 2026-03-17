// C++20: lambda in unevaluated context (decltype)
using F = decltype([](int x) { return x + 1; });

int main()
{
  F f;
  int r = f(41);
  (void)r;
}
