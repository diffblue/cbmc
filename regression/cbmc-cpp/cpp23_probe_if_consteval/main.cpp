// N5008 [stmt.if]: if consteval.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int f()
{
  if consteval
  {
    return 1;
  }
  else
  {
    return 2;
  }
}
int main()
{
  constexpr int c = f();
  int r = f();
  __CPROVER_assert(c == 1 && r == 2, "if consteval");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
