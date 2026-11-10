// C++20 template lambda
int main()
{
  auto f = []<typename T>(T x) -> T { return x; };
  int r = f(42);
  __CPROVER_assert(r == 42, "template lambda");
  return 0;
}
