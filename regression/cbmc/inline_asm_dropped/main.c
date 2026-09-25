// Statements containing an unrecognized instruction are dropped entirely by
// the remove_asm pass -- including recognized siblings in the same statement
// (see doc/cprover-manual/modeling-inline-asm.md). This test pins that no
// fence/atomic/helper-call is emitted for any of them.
int main(void)
{
  int x = 0, y = 1;

  // xchg is not modeled: the statement is dropped.
  asm volatile("xchg %0,%1" : "+r"(x), "+r"(y));

  // lock followed by an unrecognized instruction: the whole statement is
  // dropped (the atomic/fence wrapper is discarded too).
  asm volatile("lock; addl $1, %0" : "+m"(x));

  // A recognized mfence combined with an unrecognized addl: *both* are
  // dropped, not just the addl.
  asm volatile("mfence; addl $1, %0" : "+m"(x));

  return 0;
}
