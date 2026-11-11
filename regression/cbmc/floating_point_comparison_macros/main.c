// C17 7.12.14: the comparison macros (GCC's and Clang's __builtin_isless etc.)
// take arguments of any real floating type.
#include <assert.h>
#include <math.h>
int main()
{
  double a = 1, b = 2, n = NAN;
  float f = 3;
  long double l = 1e400L;
  assert(isless(a, b) && !isless(b, a) && islessequal(a, a));
  assert(isgreater(f, a) && isgreaterequal(l, a));
  assert(islessgreater(a, b) && !islessgreater(a, a));
  assert(isunordered(a, n) && !isunordered(a, b) && !isless(a, n));
  assert(__builtin_isless(a, l));
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
