extern "C" void __CPROVER_assert(bool, const char *);
enum class errc
{
  ok = 0,
  bad = 1
};
enum plain
{
  first = 0,
  second = 1
};
errc make()
{
  return {};
}
int main()
{
  errc e = errc::bad;
  e = {};
  __CPROVER_assert(
    e == errc::ok, "assignment of {} value-initializes a scoped enum");
  int i = 5;
  i = {};
  __CPROVER_assert(i == 0, "assignment of {} to an int");
  double d = 2.5;
  d = {};
  __CPROVER_assert(d == 0.0, "assignment of {} to a double");
  bool b = true;
  b = {};
  __CPROVER_assert(!b, "assignment of {} to a bool");
  plain p = second;
  p = {};
  __CPROVER_assert(p == first, "assignment of {} to an unscoped enum");
  __CPROVER_assert(make() == errc::ok, "return {} of a scoped enum");
  __CPROVER_assert(e == errc::bad, "WRONG (must FAIL)");
}
