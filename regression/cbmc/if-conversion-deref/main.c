// Soundness check for if-conversion: rewriting `if(p) x = *p;` into
// `x = p ? *p : x` must keep the dereference guarded by the condition, so
// that the NULL-pointer check does not fire on the path where the branch is
// not taken. With p constrained to be NULL, the original program never
// dereferences and verification succeeds; an unsound conversion that
// evaluates `*p` unconditionally would report a spurious NULL dereference.

int main(void)
{
  int *p;
  __CPROVER_assume(p == (int *)0);

  int x = 0;
  if(p != (int *)0)
    x = *p;

  __CPROVER_assert(x == 0, "x is unchanged when p is NULL");

  return 0;
}
