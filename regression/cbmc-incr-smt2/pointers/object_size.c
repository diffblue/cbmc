#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

int main()
{
  uint16_t x;
  uint32_t y;
  bool nondet_bool1;
  void *ptr = nondet_bool1 ? (&x) : (&y);
  size_t size = __CPROVER_OBJECT_SIZE(ptr);
  __CPROVER_assert(size == 2 || size == 4, "Expected int sizes.");
  __CPROVER_assert(size == 2, "Size is always 2. (Can be disproved.)");
  __CPROVER_assert(size == 4, "Size is always 4. (Can be disproved.)");
  size_t null_size = __CPROVER_OBJECT_SIZE(NULL);
  __CPROVER_assert(null_size == 254, "Size of NULL.");
}
