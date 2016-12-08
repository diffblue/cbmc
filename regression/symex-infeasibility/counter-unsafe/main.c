// Similar to SV-COMP'14 (loops/count_up_down_false.c) except
// that we use explicit signedness constraints to support
// benchmarks with tools that are not bit precise.

#include <assert.h>

#define N 10
#define ENABLE_CPROVER

#ifdef ENABLE_KLEE
#include <klee/klee.h>
#endif

#ifdef ENABLE_CPROVER
int nondet_int();
#endif

// It suffices to unwind N times
int main() {
#ifdef ENABLE_CPROVER
  int n = nondet_int();
  __CPROVER_assume(0 <= n && n < N);
#elif ENABLE_KLEE
  int n;
  klee_make_symbolic(&n, sizeof(n), "n");
  if (0 > n)
    return 0;
  if (n >= N)
    return 0;
#endif

  int x = n, y = 0;
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  assert(0 <= y && y != n);
  return 0;
}
