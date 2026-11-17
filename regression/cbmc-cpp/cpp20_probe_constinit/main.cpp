// N5008 [dcl.constinit]: a constinit variable.
extern "C" void __CPROVER_assert(bool, const char *);
constinit int g = 5;
int main()
{
  __CPROVER_assert(g == 5, "constinit");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
