#include <assert.h>
#include <stdbool.h>

void test_function(void *input)
{
  assert(input == 0);
}

void test_void_array(void *input_array[10])
{
  __CPROVER_assume(input_array != 0);
  assert(input_array[0] == 0);
  assert(false);
}

void test_ptr_array(void **input_array)
{
  __CPROVER_assume(input_array != 0);
  assert(input_array[0] == 0);
  assert(false);
}
