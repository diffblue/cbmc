#include <assert.h>
#include <math.h>

int main()
{
  assert(round(1.1) == 1.0);
  assert(round(1.5) == 2.0);
  assert(round(1.9) == 2.0);
  assert(round(-1.1) == -1.0);
  assert(round(-1.5) == -2.0);
  assert(round(-1.9) == -2.0);
  assert(signbit(round(-0.0)));
  return 0;
}
