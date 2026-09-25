// C++20 template lambda — verify parsing of template parameter syntax
int main()
{
  // Template lambda with explicit template parameters (parsed, not invoked)
  auto add = []<typename T>(int a, int b) { return a + b; };
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "template lambda parsed");
  return 0;
}
