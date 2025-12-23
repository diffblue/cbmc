#include <assert.h>
#include <fenv.h>

int nondet_int();

int main()
{
  int exceptions = nondet_int();
#ifdef _MSC_VER
  // Visual Studio's fenv.h includes an inlined implementation of
  // feraiseexcept, which prevents us from using the one in
  // our library.
  __CPROVER_assert(0, "dummy assertion");
#else
  feraiseexcept(exceptions);
#endif
  return 0;
}
