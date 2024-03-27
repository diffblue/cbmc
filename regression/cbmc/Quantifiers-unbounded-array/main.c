#include <assert.h>
#include <limits.h>
#include <stdlib.h>

size_t nondet_size_t();

int main()
{
  size_t size = nondet_size_t();
  __CPROVER_assume(0 < size);

  // avoids overflows in the loop body on i * 2
  __CPROVER_assume(size < INT_MAX / 2);
  size_t nof_bytes = size * sizeof(int);
  int *arr = malloc(nof_bytes);
  __CPROVER_assume(arr);
  __CPROVER_array_set(arr, 0);

  // jump to a nondet state
  size_t i = nondet_size_t();
  __CPROVER_assume(i < size);
  __CPROVER_havoc_object(arr);

  // assume loop invariant
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });

  arr[i] = arr[i] + i * 2;
  i += 1;

  assert(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });
}
