// C++17 constexpr lambda
int main()
{
  auto f = [](int x) constexpr { return x * 2; };
  int r = f(21);
  __CPROVER_assert(r == 42, "constexpr lambda");
  return 0;
}
