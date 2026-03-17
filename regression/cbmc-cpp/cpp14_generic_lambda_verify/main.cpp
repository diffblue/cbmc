// C++14 generic lambda
int main()
{
  auto add = [](auto a, auto b) { return a + b; };
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "generic lambda int");
  double d = add(1.0, 2.0);
  __CPROVER_assert(d == 3.0, "generic lambda double");
  return 0;
}
