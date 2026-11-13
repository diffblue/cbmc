// N5008 [expr.type.conv]: auto(x), a decay-copy.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a = 3;
  auto b = auto(a);
  __CPROVER_assert(b == 3, "auto(x)");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
