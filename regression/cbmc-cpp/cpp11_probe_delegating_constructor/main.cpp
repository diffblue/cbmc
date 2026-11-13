// N5008 [class.base.init]: a delegating constructor.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int a, b;
  S(int x) : a(x), b(x)
  {
  }
  S() : S(7)
  {
  }
};
int main()
{
  S s;
  __CPROVER_assert(s.a == 7 && s.b == 7, "delegating constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
