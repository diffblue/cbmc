// fmin(+0, -0) should return -0 per IEEE 754-2019
// The C library model uses (f <= g || isnan(g)) ? f : g
// Since +0 <= -0 is true, it returns f = +0 instead of -0.
#include <assert.h>
#include <math.h>

int main()
{
  float r = fminf(+0.0f, -0.0f);
  assert(signbit(r));
  return 0;
}
