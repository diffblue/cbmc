// Test that round-to-integral (rintf) works correctly under various
// rounding modes.

#include <assert.h>
#include <math.h>

extern int __CPROVER_rounding_mode;

int main()
{
  float a;

  // ROUND_TO_EVEN: tie rounds to even
  __CPROVER_assume(a == 2.5f);
  __CPROVER_rounding_mode = 0;
  float r1 = rintf(a);
  assert(r1 == 2.0f);

  float b;
  __CPROVER_assume(b == 3.5f);
  __CPROVER_rounding_mode = 0;
  float r2 = rintf(b);
  assert(r2 == 4.0f);

  // ROUND_TO_PLUS_INF
  float c;
  __CPROVER_assume(c == 2.3f);
  __CPROVER_rounding_mode = 2;
  float r3 = rintf(c);
  assert(r3 == 3.0f);

  // ROUND_TO_MINUS_INF
  float d;
  __CPROVER_assume(d == 2.7f);
  __CPROVER_rounding_mode = 1;
  float r4 = rintf(d);
  assert(r4 == 2.0f);

  // ROUND_TO_ZERO
  float e;
  __CPROVER_assume(e == -2.7f);
  __CPROVER_rounding_mode = 3;
  float r5 = rintf(e);
  assert(r5 == -2.0f);

  // Already integral
  float f;
  __CPROVER_assume(f == 42.0f);
  __CPROVER_rounding_mode = 0;
  float r6 = rintf(f);
  assert(r6 == 42.0f);

  return 0;
}
