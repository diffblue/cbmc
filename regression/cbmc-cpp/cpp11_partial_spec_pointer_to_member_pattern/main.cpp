extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int k;
  int mul2(int a)
  {
    return k * a;
  }
};
typedef int (S::*PMF2)(int);
typedef int S::*PMD;
template <class MP>
struct memfun
{
  static constexpr int n = 0;
};
template <class _Res, class _Class>
struct memfun<_Res _Class::*>
{
  static constexpr int n = 1;
};
int main()
{
  __CPROVER_assert(
    memfun<PMD>::n == 1, "data member pointer matches _Res _Class::*");
  __CPROVER_assert(
    memfun<PMF2>::n == 1, "member function pointer matches _Res _Class::*");
  __CPROVER_assert(memfun<int *>::n == 0, "plain pointer does not match");
  return 0;
}
