#include <assert.h>
#define ASSERT(x) __CPROVER_assert((x), "assertion " #x)

int *bar(int *arr_unmodified, int *arr_modified);

int main(int argc, char *argv[])
{
  int arr_x[] = {1, 2, 3, 4};
  int arr_y[] = {1, 2, 3, 4};
  int *p2arr = arr_x;

  p2arr = bar(arr_x, arr_y);
  ASSERT(*arr_y==2);
  // ASSERT(arr_y[1]==3);

  ASSERT(p2arr==arr_y);
  ASSERT(*p2arr==2);
  // ASSERT(p2arr[1]==3);
}

int *bar(int *arr_unmodified, int *arr_modified)
{
  ASSERT(*arr_unmodified==1);
  // ASSERT(arr_unmodified[1]==2);

  (*arr_modified) += 1;
  // arr_modified[1] = 3;

  ASSERT(*arr_modified==2);
  // assert(arr_modified[1]==3);

  return arr_modified;
}
