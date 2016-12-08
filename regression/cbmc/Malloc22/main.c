#include <assert.h>
#include <stdlib.h>

unsigned nondet_unsigned();

int main() {
  unsigned n = nondet_unsigned();
  __CPROVER_assume(n>0);
  unsigned pA[n];
  unsigned *p = (unsigned *)malloc(sizeof(unsigned) * n);

  for (int i=0; i<n; i++) {
    p[i] = i;
    pA[i] = i;
  }
  assert(p[n-1] == n-1);
  assert(pA[n-1] == n-1);
  assert(0);

  return 0;
}
