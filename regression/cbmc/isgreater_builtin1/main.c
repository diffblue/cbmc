#include <assert.h>
#include <math.h>

double nondet_double(void);
float nondet_float(void);

int main(void)
{
  double x = nondet_double();
  float y = nondet_float();
  if(x == 2.0 && y == 1.0f)
  {
    assert(isgreater(x, 1.0));
    assert(isgreaterequal(x, 2.0));
    assert(isless(y, 2.0f));
    assert(islessequal(y, 1.0f));
    assert(islessgreater(x, y));
    assert(!isunordered(x, y));
    assert(isunordered(x, NAN));
  }
  return 0;
}
