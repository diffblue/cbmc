// N5008 [dcl.init.aggr]/3.1, /4.2: a designated-initializer-list
// initializes the named elements, an element of class type by its
// constructor (libstdc++ 16's `constexpr leap_second_info
// __after_last{.is_leap_second = false, .elapsed = seconds(...)}').
extern "C" void __CPROVER_assert(bool, const char *);
struct sec
{
  long n;
  constexpr explicit sec(long x) : n(x)
  {
  }
};
struct info
{
  bool b;
  sec e;
  int tail = 7;
};
int f(int k)
{
  constexpr info after_last{.b = false, .e = sec(3)};
  info later{.e = sec(k)};
  return (int)after_last.e.n + (int)later.e.n + later.tail + later.b;
}
int main()
{
  __CPROVER_assert(f(1) == 11, "designated class member");
  __CPROVER_assert(f(1) == 4, "WRONG (must FAIL)");
}
