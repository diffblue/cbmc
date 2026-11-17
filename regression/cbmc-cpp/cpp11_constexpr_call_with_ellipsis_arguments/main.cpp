// N5008 [expr.call]/12: arguments beyond the parameters match the ellipsis;
// a call passing some is a constant expression if the body is
// ([expr.const]).  The overload taking `...' is the fallback of SFINAE
// dispatch, as in libstdc++'s __is_*_helper idioms.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr int any(...)
{
  return 2;
}
constexpr int first_and_more(int n, ...)
{
  return n + 1;
}
static_assert(any(1.0) == 2, "one argument for the ellipsis");
static_assert(any(1, 'c', 2.0) == 2, "three arguments for the ellipsis");
static_assert(first_and_more(2, 3.0) == 3, "a parameter and the ellipsis");
static_assert(any() == 2, "no argument");
int main()
{
  constexpr int v = first_and_more(4, 1, 2);
  __CPROVER_assert(v == 5, "constant initializer");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
