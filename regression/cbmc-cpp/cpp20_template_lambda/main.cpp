// C++20 template lambda — verify parsing of template parameter syntax
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // Template lambda with explicit template parameters.  N5008
  // [temp.deduct.call]/1: T must be deducible from the call's arguments.
  auto add = []<typename T>(T a, T b) { return a + b; };
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "template lambda parsed");
  return 0;
}
