// N5008 [conv.fctptr], [conv.ptr], [basic.fundamental]/2: int(long long)
// and int(long) are different function types even where long and long long
// have the same width, and no standard conversion turns a pointer to one
// into a pointer to the other
extern "C" void __CPROVER_assert(bool, const char *);
int f_ll(long long)
{
  return 1;
}
int f_l(long)
{
  return 2;
}
int sel(int (*)(long))
{
  return 10;
}
int sel(...)
{
  return 20;
}
static_assert(!__is_convertible(int (*)(long), int (*)(long long)), "");
static_assert(!__is_convertible(int (*)(char), int (*)(signed char)), "");
static_assert(__is_convertible(int (*)(long), int (*)(long)), "");
int main()
{
  __CPROVER_assert(sel(f_l) == 10, "the exact pointer type");
  __CPROVER_assert(sel(f_ll) == 20, "a different parameter type");
  __CPROVER_assert(sel(f_ll) == 10, "WRONG (must FAIL)");
  return 0;
}
