extern "C" void __CPROVER_assert(bool, const char *);
struct result
{
  bool ok;
  int value;
  explicit operator bool() const
  {
    return ok;
  }
};
int f(bool ok)
{
  // [stmt.pre]/1: the initializer of a condition declaration is a
  // brace-or-equal-initializer
  if(const result r = {ok, 4})
    return r.value;
  if(int x{2})
    return -x;
  return 0;
}
int main()
{
  __CPROVER_assert(f(true) == 4, "copy-list-initialization");
  __CPROVER_assert(f(false) == -2, "direct-list-initialization");
  int n = 0;
  while(result r{n < 3, n})
    n = r.value + 1;
  __CPROVER_assert(n == 3, "while");
  switch(int k{5})
  {
  case 5:
    n = k;
    break;
  default:
    n = 0;
  }
  __CPROVER_assert(n == 5, "switch");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
