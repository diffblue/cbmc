// N5008 [stmt.if]/4: `if consteval' executes its first substatement in a
// manifestly constant-evaluated context and the else substatement
// otherwise; `if !consteval' the other way round.  Within the consteval branch an immediate
// function may be called (an immediate function context, [expr.const]/16).
extern "C" void __CPROVER_assert(bool, const char *);
consteval int sq(int x)
{
  return x * x;
}
constexpr int f(int x)
{
  if consteval
  {
    return sq(x);
  }
  else
  {
    return -x;
  }
}
constexpr int g(int x)
{
  if !consteval
  {
    return 1;
  }
  else
  {
    if(x > 0)
      return 2;
    return 3;
  }
}
constexpr int h()
{
  int r = 0;
  if consteval
  {
    r = 5;
  }
  return r;
}
static_assert(f(3) == 9);
static_assert(g(1) == 2 && g(-1) == 3);
static_assert(h() == 5);
int main()
{
  int x = 3;
  __CPROVER_assert(f(x) == -3 && g(x) == 1 && h() == 0, "at run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
