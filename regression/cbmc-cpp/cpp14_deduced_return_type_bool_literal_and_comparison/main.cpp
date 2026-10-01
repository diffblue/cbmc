extern "C" void __CPROVER_assert(bool, const char *);
// [dcl.spec.auto.general]/10 (the return statements must deduce the same
// type) with [expr.rel]/2 and [expr.eq]/1: `true' and `st == 0' are both
// prvalues of type bool (libc++'s __stop_state::__add_callback lambda)
auto f(int st)
{
  if(st != 0)
    return true;
  return st == 0;
}
int main()
{
  const auto g = [](int st)
  {
    if((st & 1) != 0)
      return true;
    return (st >> 1) < 1;
  };
  __CPROVER_assert(f(1) && f(0), "function");
  __CPROVER_assert(g(1) && g(0) && !g(2), "lambda");
  __CPROVER_assert(!f(1), "WRONG (must FAIL)");
}
