// N5008 [dcl.spec.auto.general]: a deduced return type.
extern "C" void __CPROVER_assert(bool, const char *);
auto f(int x)
{
  return x * 2;
}
int main()
{
  __CPROVER_assert(f(3) == 6, "deduced return type");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
