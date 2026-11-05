// N5008 [expr.prim.lambda.capture]: a lambda captures by reference.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int k = 2;
  auto f = [&k](int x) { return x * k; };
  k = 5;
  __CPROVER_assert(f(3) == 15, "capture by reference");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
