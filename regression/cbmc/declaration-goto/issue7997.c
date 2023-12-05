#include <assert.h>

extern void __VERIFIER_assume(int cond);
extern int __VERIFIER_nondet_int(void);

int main(void)
{
  if(__VERIFIER_nondet_int())
    goto switch_2_1;
  int tmp_ndt_4 = __VERIFIER_nondet_int();
  __VERIFIER_assume(__VERIFIER_nondet_int());
  __VERIFIER_assume(tmp_ndt_4 == 1);
switch_2_1:
  assert(tmp_ndt_4 > 0);
  return 0;
}
