#include <assert.h>
#include <stdlib.h>

size_t
find_first_set(const size_t max_malloc_size, const size_t bits_accumulator)
{
  if(max_malloc_size & 1)
    return bits_accumulator;
  return find_first_set(max_malloc_size >> 1, bits_accumulator + 1);
}

size_t calculate_object_bits()
{
  const size_t ptr_size = sizeof(void *) * 8;
  return ptr_size - find_first_set(__CPROVER_max_malloc_size, 1);
}

int main()
{
  void *temp = malloc(2);
  size_t object_bits = calculate_object_bits();
  assert(object_bits != 6);
  assert(object_bits != 8);
  assert(object_bits != 10);
  __CPROVER_assume("end of main.");
}
