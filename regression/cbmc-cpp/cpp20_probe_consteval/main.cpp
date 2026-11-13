// N5008 [dcl.constexpr]: a call of an immediate function.
extern "C" void __CPROVER_assert(bool, const char *);
consteval int sq(int x)
{
  return x * x;
}
int main()
{
  __CPROVER_assert(sq(3) == 9, "consteval call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
