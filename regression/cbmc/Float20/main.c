/*
** float-rounder-bug.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 20/05/13
**
** Another manifestation of the casting bug.
** If the number is in (0,0x1p-126) it is rounded to zero rather than a subnormal number.
*/
#define FULP 1

void bug (float min) {
  __CPROVER_assume(min == 0x1.fffffep-105f);
  float modifier = (0x1.0p-23 * (1<<FULP));
  float ulpdiff = min * modifier;

  assert(ulpdiff == 0x1p-126f);    // Should be true

  return;
}

void bugBrokenOut (float min) {
  __CPROVER_assume(min == 0x1.fffffep-105f);
  float modifier = (0x1.0p-23 * (1<<FULP));
  double dulpdiff = (double)min * (double)modifier;  // Fine up to here
  float ulpdiff = (float)dulpdiff;  // Error

  assert(ulpdiff == 0x1p-126f); // Should be true

  return;
}

void bugCasting (double d) {
  __CPROVER_assume(d == 0x1.fffffep-127);

  float f = (float) d;

  assert(f == 0x1p-126f); // Should be true

  return;
}

int main (void) {
  float f = __VERIFIER_nondet_float();
  bug(f);

  float g = __VERIFIER_nondet_float();
  bugBrokenOut(g);

  double d = __VERIFIER_nondet_double();
  bugCasting(d);

  return 1;
}
