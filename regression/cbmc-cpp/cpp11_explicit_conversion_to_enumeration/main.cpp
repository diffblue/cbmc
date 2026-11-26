extern "C" void __CPROVER_assert(bool, const char *);
enum flag
{
  off = 0,
  on = 1
};
enum class level : unsigned char
{
  low = 1,
  high = 2
};
flag from_bool(bool b)
{
  return (flag)b;
}
int main()
{
  // [expr.static.cast]/9: bool is an integral type, and a floating-point
  // value converts via the underlying type
  __CPROVER_assert(from_bool(true) == on && from_bool(false) == off, "bool");
  __CPROVER_assert(static_cast<flag>(true) == on, "static_cast bool");
  double d = 2.75;
  __CPROVER_assert(static_cast<level>(d) == level::high, "double");
  __CPROVER_assert((flag)0.5f == off, "float");
  __CPROVER_assert(level(1.5) == level::low, "functional cast");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
