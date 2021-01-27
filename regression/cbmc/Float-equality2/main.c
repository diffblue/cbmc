#include <assert.h>
#include <math.h>

int main()
{
  float a;
  float b;
  // We could do "if (isnormal(a) && isnormal(b))", but __CPROVER_isnanf(a+b)
  // will permit solving this entirely via the simplifier, if, and only if, the
  // equality is successfully simplified (despite the different order of
  // operands).
  assert(__CPROVER_isnanf(a + b) || a + b == b + a);
}
