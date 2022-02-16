#include <stdint.h>
#include <stdlib.h>

// byte-level comparison
#define CHECK_SLICE(A, OLD_A, I, IDX, HAVOC_SIZE)                              \
  {                                                                            \
    __CPROVER_assert(                                                          \
      !(IDX <= I && I <= IDX + HAVOC_SIZE) | A[I] == OLD_A[I],                 \
      "expecting FAILURE");                                                    \
                                                                               \
    __CPROVER_assert(                                                          \
      (IDX <= I && I <= IDX + HAVOC_SIZE) | A[I] == OLD_A[I],                  \
      "expecting SUCCESS");                                                    \
  }

// ARRAY WITH SYMBOLIC SIZE.
void main(void)
{
  // INITIALIZE
  uint32_t size;
  __CPROVER_assume(5 == size);

  char a[size];
  char old_a[size];

  __CPROVER_array_set(a, 0);
  __CPROVER_array_set(old_a, 0);

  uint32_t idx;
  __CPROVER_assume(idx < size);

  uint32_t havoc_size;
  __CPROVER_assume(1 <= havoc_size && havoc_size <= size);
  __CPROVER_assume(idx + havoc_size <= size);

  // HAVOC SINGLE CELL
  __CPROVER_havoc_slice(&a[idx], havoc_size);

  // POSTCONDITIONS
  CHECK_SLICE(a, old_a, 0, idx, havoc_size);
  CHECK_SLICE(a, old_a, 1, idx, havoc_size);
  CHECK_SLICE(a, old_a, 2, idx, havoc_size);
  CHECK_SLICE(a, old_a, 3, idx, havoc_size);
  CHECK_SLICE(a, old_a, 4, idx, havoc_size);
  return;
}
