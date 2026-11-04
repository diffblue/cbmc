#include <assert.h>
#include <fenv.h>

// C11 7.6.3.2p2: "If the argument is not equal to the value of a rounding
// direction macro, the rounding direction is not changed."
// C11 7.6.3.2p3: "The fesetround function returns zero if and only if the
// requested rounding direction was established."

int main(void)
{
#ifdef FE_DOWNWARD
  // Set a known mode first.
  int r1 = fesetround(FE_DOWNWARD);
  assert(r1 == 0);
  assert(fegetround() == FE_DOWNWARD);

  // Attempt to set an invalid mode (42 is not FE_*).
  int r2 = fesetround(42);
  // Must report failure.
  assert(r2 != 0);
  // The rounding direction must remain FE_DOWNWARD.
  assert(fegetround() == FE_DOWNWARD);
#endif

  return 0;
}
