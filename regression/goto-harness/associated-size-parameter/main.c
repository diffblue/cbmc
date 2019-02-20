#include <assert.h>

void test(int *array, int size)
{
  for(int i = 0; i < size; i++)
    array[i] = i;

  for(int i = 0; i < size; i++)
    assert(array[i] == i);
}
