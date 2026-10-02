extern "C" void __CPROVER_assert(bool, const char *);
struct ord
{
};
struct unspec
{
  unspec(int *)
  {
  }
};
struct count
{
  count(ord)
  {
  }
  count(int)
  {
  }
};
// [over.match.best]/2.1, [over.ics.rank]/3.3: for eq(o, 0) the first
// candidate is better for the first argument (identity against a
// user-defined conversion); for the second, `0 -> unspec' (through
// unspec(int *)) and `0 -> count' (through count(int)) use different
// constructors and are indistinguishable -- so the first candidate is best
int eq(ord, unspec)
{
  return 1;
}
int eq(count, count)
{
  return 2;
}
int main()
{
  ord o;
  __CPROVER_assert(eq(o, 0) == 1, "first argument decides");
  __CPROVER_assert(eq(o, 0) != 1, "WRONG (must FAIL)");
}
