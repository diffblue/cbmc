#include <assert.h>

// Edge case: const array parameter
// const int arr[] is equivalent to const int *arr
void havoc_const_array(const int arr[], int size);

int main(void)
{
  int data[] = {1, 2, 3, 4, 5};

  assert(data[0] == 1);
  assert(data[1] == 2);
  assert(data[2] == 3);
  assert(data[3] == 4);
  assert(data[4] == 5);

  // Array parameter with const should not allow modification of elements
  havoc_const_array(data, 5);

  // All should succeed due to const
  assert(data[0] == 1);
  assert(data[1] == 2);
  assert(data[2] == 3);
  assert(data[3] == 4);
  assert(data[4] == 5);

  return 0;
}
