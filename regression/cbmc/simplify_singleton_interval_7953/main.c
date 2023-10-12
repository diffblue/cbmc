#include <assert.h>
extern void __VERIFIER_assume(int cond);
extern int __VERIFIER_nondet_int(void);
int main()
{
  int z = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  __VERIFIER_assume(1 < z);
  __VERIFIER_assume(1 <= z && k <= 1);
  assert(0);
}
