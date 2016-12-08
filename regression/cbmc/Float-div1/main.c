#include <assert.h>
#include <math.h>

#ifdef __GNUC__
void inductiveStepHunt (float startState)
{
  float target = 0x1.fffffep-3f;

  __CPROVER_assume((0 < startState) && (fpclassify(startState) == FP_NORMAL) && (0x1p-126f <= startState));

  float secondPoint = (target / startState);

  float nextState = (startState + secondPoint) / 2;

  float oneAfter = (target / nextState);

  assert(oneAfter > 0);
}

void simplifiedInductiveStepHunt (float nextState)
{
  float target = 0x1.fffffep-3f;

  // Implies nextState == 0x1p+124f;
  __CPROVER_assume((0x1.fffffep+123f < nextState) && (nextState < 0x1.000002p+124f));

  float oneAfter = (target / nextState);

  // Is true and correctly proven by constant evaluation
  // Note that this is the smallest normal number
  assert(0x1.fffffep-3f / 0x1p+124f == 0x1p-126f);

  assert(oneAfter > 0);
}
#endif

int main (void)
{
  #ifdef __GNUC__
  //  inductiveStepHunt(0x1p+125f);
  //  simplifiedInductiveStepHunt(0x1p+124f);

  float f, g;

  inductiveStepHunt(f);
  simplifiedInductiveStepHunt(g);
  #endif

  return 0;
}
