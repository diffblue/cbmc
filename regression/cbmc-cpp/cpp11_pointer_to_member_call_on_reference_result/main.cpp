extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int k;
  int mul(int a) const
  {
    return k * a;
  }
};
typedef int (S::*PMF)(int) const;
S g_s;
S &ref()
{
  return g_s;
}
S *ptr()
{
  return &g_s;
}
template <class T>
T &&dv() noexcept;
int main()
{
  g_s.k = 3;
  PMF f = &S::mul;
  __CPROVER_assert((ref().*f)(5) == 15, "(ref().*f)(5)");
  __CPROVER_assert((ptr()->*f)(5) == 15, "(ptr()->*f)(5)");
  decltype((dv<S &>().*f)(5)) r = 1;
  __CPROVER_assert(r == 1, "decltype (dv<S&>().*f)(5)");
  decltype((dv<S &>().*dv<PMF &>())(dv<int>())) r2 = 2;
  __CPROVER_assert(r2 == 2, "decltype (dv<S&>().*dv<PMF&>())(dv<int>())");
  return 0;
}
