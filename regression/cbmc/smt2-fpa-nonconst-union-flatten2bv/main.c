// Reproducer for #9101: flatten2bv aborts on non-constant FPA-encoded float
// when exporting to SMT2 with --fpa.
//
// The classic union-based float-to-int type-punning idiom (used pervasively
// in bit-exact libm code) triggers an invariant violation in the SMT2 export
// path because flatten2bv does not handle non-constant floatbv expressions
// under FPA theory.  The native (SAT) back-end solves this without issue.

extern void reach_error(void);
extern float __VERIFIER_nondet_float(void);

int main(void)
{
  float f = __VERIFIER_nondet_float();
  union
  {
    float f;
    unsigned u;
  } pun;
  pun.f = f;
  if((pun.u & 0x7fffffffu) > 0x7f800000u)
    reach_error();
  return 0;
}
