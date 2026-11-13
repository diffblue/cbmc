// C++23 language features require GCC 11+
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
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

#else
int main()
{
}
#endif
