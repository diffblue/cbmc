// C++20 template lambda
int main()
{
  auto f = []<typename T>(T x) { return x + 1; };
  __CPROVER_assert(f(41) == 42, "lambda template");
}
