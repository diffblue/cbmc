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
#elif ENABLE_KLEE
  int k;
  klee_make_symbolic(&k, sizeof(k), "k");
#endif

  for(int n = 0; n < N; n = n + 1) {
    if(k == 7) {
      k = 0;
    }
    k = k + 1;
  }

  assert(k <= 7);
}
