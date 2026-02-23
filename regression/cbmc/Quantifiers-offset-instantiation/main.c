#include <assert.h>
#include <stdlib.h>

size_t nondet_size_t();

int main()
{
  size_t n = nondet_size_t();
  __CPROVER_assume(n > 2 && n < 100);
  int *arr = malloc(n * sizeof(int));
  __CPROVER_assume(arr);

  arr[0] = 0;

  // forall j: 0 <= j < n-1 => arr[j+1] == arr[j] + 1
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(j < n - 1) || (arr[j + 1] == arr[j] + 1)
  });

  assert(arr[1] == 1);
  assert(arr[2] == 2);
}
