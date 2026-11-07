// N5008 [expr.prim.lambda.closure]: a generic lambda called with int and
// double.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto f = [](auto a, auto b) { return a + b; };
  __CPROVER_assert(f(1, 2) == 3 && f(1.5, 1.5) == 3.0, "generic lambda");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
