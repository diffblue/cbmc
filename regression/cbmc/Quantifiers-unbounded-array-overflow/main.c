#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

size_t nondet_size_t();

#if UINT_MAX < SIZE_MAX
#  define SMALLER_TYPE int
#else
#  define SMALLER_TYPE short
#endif

// The model has an overflow, falsified instantly with SAT,
// takes forever with z3 because of the quantifiers
int main()
{
  size_t size = nondet_size_t();
  __CPROVER_assume(0 < size);
  __CPROVER_assume(size <= __CPROVER_max_malloc_size / sizeof(SMALLER_TYPE));
  // we remove this assumption, which in turn allows to cause an integer
  // overflow in the loop body when computing i*2, because we would end up
  // comparing i*2, which does not overflow on size_t, to the overflowed
  // (wrap-around) value when i*2 was assigned to the int-typed array element
  // __CPROVER_assume(size < INT_MAX / 2);
  size_t nof_bytes = size * sizeof(SMALLER_TYPE);
  SMALLER_TYPE *arr = malloc(nof_bytes);
  __CPROVER_assume(arr);
  __CPROVER_array_set(arr, 0);

  // None of this should overflow because initially arr[j] == 0 for all j

  // the original loop
  // size_t i = 0;
  // while (i < size)
  // __CPROVER_loop_invariant(i <= size)
  // __CPROVER_loop_invariant(__CPROVER_forall {size_t j; !(j < i) || (arr[j] == j * 2) })
  // __CPROVER_loop_invariant(__CPROVER_forall {size_t j; !(i <= j && j < size) || (arr[j] == 0) })
  // {
  //     arr[i] = arr[i] + 2 * i;
  //     i += 1;
  // }

  size_t i = 0;

  // check base case
  assert(i <= size);
  assert(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });
  assert(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });

  // jump to a nondet state
  i = nondet_size_t();
  __CPROVER_havoc_object(arr);

  // assume loop invariant
  __CPROVER_assume(i <= size);
  __CPROVER_assume(i <= size);
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });

  size_t old_i = i;
  if(i < size)
  {
    arr[i] = arr[i] + i * 2;
    i += 1;

    // check loop invariant post loop step
    assert(i <= size);
    assert(__CPROVER_forall {
      size_t j;
      !(j < i) || (arr[j] == j * 2)
    });
    assert(__CPROVER_forall {
      size_t j;
      !(i <= j && j < size) || (arr[j] == 0)
    });
    __CPROVER_assume(0); // stop progress
  }

  // check that the loop invariant holds post loop
  assert(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });

  assert(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });
}
