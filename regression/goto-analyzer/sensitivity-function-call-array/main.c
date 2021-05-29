#include <assert.h>

int *bar(int *arr_unmodified, int *arr_modified);

int main()
{
  int arr_x[] = {1, 2, 3, 4};
  int arr_y[] = {1, 2, 3, 4};
  int *p2arr = arr_x;

  p2arr = bar(arr_x, arr_y);
  assert(*arr_y == 2);
  // assert(arr_y[1]==3);

  assert(p2arr == arr_y);
  assert(*p2arr == 2);
  // assert(p2arr[1]==3);
}

int *bar(int *arr_unmodified, int *arr_modified)
{
  assert(*arr_unmodified == 1);
  // assert(arr_unmodified[1]==2);

  (*arr_modified) += 1;
  // arr_modified[1] = 3;

  assert(*arr_modified == 2);
  // assert(arr_modified[1]==3);

  return arr_modified;
}
