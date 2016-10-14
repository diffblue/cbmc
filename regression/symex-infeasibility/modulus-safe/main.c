#include <assert.h>

#define N 20

#define ENABLE_CPROVER
#ifdef ENABLE_KLEE
#include <klee/klee.h>
#endif

#ifdef ENABLE_CPROVER
int nondet_int();
#endif

int main(void) {
#ifdef ENABLE_CPROVER
  int k = nondet_int();
  __CPROVER_assume(0 <= k && k < 7);
#elif ENABLE_KLEE
  int k;
  klee_make_symbolic(&k, sizeof(k), "k");

  if (0 > k)
    return 0;
  if (k >= 7)
    return 0;
#endif

  for(int n = 0; n < N; n = n + 1) {
    if(k == 7) {
      k = 0;
    }
    k = k + 1;
  }

#ifndef FORCE_BRANCH
  assert(k <= 7);
#endif
}
