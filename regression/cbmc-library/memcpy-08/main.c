#include <stdlib.h>
#include <string.h>

int __VERIFIER_nondet_int();

void main()
{
  size_t size;
  __CPROVER_assume(size >= 2);
  // limit the size to ensure size * sizeof(int) wouldn't overflow, and we don't
  // reach the maximum object size
  __CPROVER_assume(size <= 1000);

  int *dest_buffer = malloc(size * sizeof(int));
  int *src_buffer = malloc(size * sizeof(int));
  src_buffer[0] = 42;
  src_buffer[1] = __VERIFIER_nondet_int();

  memcpy(dest_buffer, src_buffer, size * sizeof(int));
  __CPROVER_assert(dest_buffer[0] == 42, "should pass");
  __CPROVER_assert(dest_buffer[1] == 42, "should fail");
}
