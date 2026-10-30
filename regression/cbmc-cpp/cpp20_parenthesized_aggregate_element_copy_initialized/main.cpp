extern "C" void __CPROVER_assert(bool, const char *);
struct to_int
{
  explicit operator int() const
  {
    return 1;
  }
};
struct aggregate
{
  int v;
};
// N5008 [dcl.init.general]/16.6.2.2, [dcl.init.aggr]/4.2,
// [over.match.copy]/1.2: in the parenthesized aggregate initialization
// `aggregate a(e)' the element v is copy-initialized from e, which does not
// use the explicit conversion function
int main()
{
  __CPROVER_assert(
    !__is_constructible(aggregate, to_int) &&
      __is_constructible(aggregate, int) && __is_constructible(int, to_int),
    "element copy-initialized");
  __CPROVER_assert(__is_constructible(aggregate, to_int), "WRONG (must FAIL)");
  return 0;
}
