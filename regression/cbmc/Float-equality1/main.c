#include <assert.h>

void main()
{
  double a = __VERIFIER_nondet_double(), b = __VERIFIER_nondet_double(),
         c = __VERIFIER_nondet_double();
  __CPROVER_assume(a + b > c);
#ifdef EQUALITY
  double x = a, y = b, z = c;
  assert(!(z > x + y));
#else
  assert(!(c > a + b));
#endif
}
