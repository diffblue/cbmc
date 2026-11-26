// N5008 [dcl.constexpr]: a constexpr function with a loop and a local
// variable.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int f(int n)
{
  int s = 0;
  for(int i = 0; i < n; ++i)
    s += i;
  return s;
}
static_assert(f(4) == 6, "constant evaluation");
int main()
{
  __CPROVER_assert(f(5) == 10, "constexpr loop at run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
