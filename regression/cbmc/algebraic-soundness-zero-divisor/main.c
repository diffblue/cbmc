int main()
{
  // Item 13 / Bug B soundness regression.
  // Over ZMod(2^8) there exist zero divisors: 16*16 == 0 with both
  // factors non-zero. So {a*b==0, a!=0, b!=0} is satisfiable and
  // the assert(0) is reachable -> VERIFICATION FAILED. The algebraic
  // pre-solver previously refuted this via the Rabinowitsch
  // unit-trick (a!=0 encoded as a*e==1, i.e.\ "a is a unit"), which
  // is unsound over ZMod(2^8), and wrongly reported SUCCESSFUL.
  __CPROVER_bitvector[8] a, b, r;
  r = a * b;
  __CPROVER_assume(r == 0);
  __CPROVER_assume(a != 0);
  __CPROVER_assume(b != 0);
  __CPROVER_assert(0, "zero divisors exist (must be FAILED)");
}
