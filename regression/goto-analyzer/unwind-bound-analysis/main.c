#include <assert.h>

/*
 ./goto-analyzer/goto-analyzer ../regression/goto-analyzer/unwind-bound-analysis/main.c --verify --vsd --loop-unwind 258 --recursive-interprocedural --vsd-arrays every-element --vsd-array-max-elements 18 --one-domain-per-history --vsd-values intervals --verbosity 10 | grep -v __CPROVER_ | less

bugs
- still got a problem with argv
- when the first branch is not taken, the domain is not pruned enough
- somehow when the paths exit the interval is off-by-one

*/

#define BUFFERLENGTH 16

int main ()
{
  int n;
  __CPROVER_assume(n < BUFFERLENGTH);
  int array[BUFFERLENGTH];
  
  for (int i = 0; i < n; ++i) {
    array[i] = 0;
  }

  for (int i = 0; i < n; ++i) {
    assert(array[i] == 0);
  }

  return 0;
}
