extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
struct S
{
  int k;
  int mul(int a) const
  {
    return k * a;
  }
  int mul2(int a)
  {
    return k * a;
  }
  int vol(int a) volatile
  {
    return k + a;
  }
};
// N5008 [dcl.fct]/6-7: the cv-qualifier-seq after the parameter list is part
// of the function type; the alias-declaration spelling must denote the same
// type as the typedef spelling.
using PMF = int (S::*)(int) const;
typedef int (S::*TPMF)(int) const;
using PMF2 = int (S::*)(int);
using PMFV = int (S::*)(int) volatile;
int main()
{
  __CPROVER_assert(
    std::is_same<PMF, TPMF>::value, "alias == typedef (const pmf)");
  __CPROVER_assert(
    std::is_same<PMF2, int (S::*)(int)>::value, "alias non-const pmf");
  S s;
  s.k = 3;
  PMF f = &S::mul;
  __CPROVER_assert((s.*f)(5) == 15, "call through alias const pmf");
  PMF2 g = &S::mul2;
  __CPROVER_assert((s.*g)(5) == 15, "call through alias non-const pmf");
  PMFV v = &S::vol;
  __CPROVER_assert((s.*v)(5) == 8, "call through alias volatile pmf");
  return 0;
}
