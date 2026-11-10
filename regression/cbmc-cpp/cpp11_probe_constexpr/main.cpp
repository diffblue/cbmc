// N5008 [dcl.constexpr]: a recursive constexpr function, constant-evaluated
// and called at run time.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int f(int n)
{
  return n <= 1 ? 1 : n * f(n - 1);
}
static_assert(f(5) == 120, "constant evaluation");
int main()
{
  __CPROVER_assert(f(4) == 24, "constexpr function at run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
