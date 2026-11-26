// The inner loop is entered by an unconditional forward goto that is reached
// with a non-true guard on the second outer iteration, so with --paths this
// goto takes the unconditional-goto fast path via the path-exploration
// condition. The inner loop's unwinding counter must restart on each entry:
// it runs 3 times per outer iteration, so --unwind 3 suffices.
int nondet_int(void);

int main(void)
{
  int i = 0;
  int n = nondet_int();
  __CPROVER_assume(n >= 1 && n <= 2);
outer:;
  int j = 0;
  goto inner;
  return 1;
inner:
  j++;
  if(j < 3)
    goto inner;
  i++;
  if(i < n)
    goto outer;
  return 0;
}
