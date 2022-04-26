#include <assert.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
  unsigned long size;
  __CPROVER_assume(size < 100 && size > 10);
  int *array = malloc(size * sizeof(int));
  array[size - 1] = 42;
  int fixed_array[] = {1, 2};
  __CPROVER_array_replace(array, fixed_array);
  assert(array[0] == 1);
  assert(array[1] == 2);
  assert(array[size - 1] == 42);
  assert(array[0] == 0);
}
