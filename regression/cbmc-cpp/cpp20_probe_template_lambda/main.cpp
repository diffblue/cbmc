// N5008 [expr.prim.lambda.general]: a lambda with a template parameter list.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto f = []<class T>(T) { return sizeof(T); };
  __CPROVER_assert(
    f(1) == sizeof(int), "lambda with a template parameter list");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
