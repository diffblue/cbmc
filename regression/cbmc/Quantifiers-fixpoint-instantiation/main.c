#include <assert.h>
#include <stdlib.h>

size_t nondet_size_t();

int main()
{
  size_t n = nondet_size_t();
  __CPROVER_assume(n >= 3 && n < 100);
  int *arr = malloc(n * sizeof(int));
  __CPROVER_assume(arr);

  arr[0] = 1;

  // forall j < n-1: arr[j] > 0 => arr[j+1] > 0
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(j < n - 1) || !(arr[j] > 0) || (arr[j + 1] > 0)
  });

  // Requires chained instantiation: j=0 gives arr[1]>0, j=1 gives arr[2]>0
  assert(arr[2] > 0);
}
