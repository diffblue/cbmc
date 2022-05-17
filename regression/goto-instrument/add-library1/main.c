#include <math.h>

int main()
{
  float f;
  __CPROVER_assume(isnormal(f));
  __CPROVER_assert(ceilf(f) >= f, "ceil rounds upwards");
}
