int *bar(int *arr_unmodified, int *arr_modified);

int main()
{
  int arr_x[] = {1, 2, 3, 4};
  int arr_y[] = {1, 2, 3, 4};
  int *p2arr = arr_x;

  p2arr = bar(arr_x, arr_y);
  __CPROVER_assert(*arr_y == 2, "assertion *arr_y == 2");
  // __CPROVER_assert(arr_y[1]==3, "assertion arr_y[1]==3");

  __CPROVER_assert(p2arr == arr_y, "assertion p2arr == arr_y");
  __CPROVER_assert(*p2arr == 2, "assertion *p2arr == 2");
  // __CPROVER_assert(p2arr[1]==3, "assertion p2arr[1]==3");
}

int *bar(int *arr_unmodified, int *arr_modified)
{
  __CPROVER_assert(*arr_unmodified == 1, "assertion *arr_unmodified == 1");
  // __CPROVER_assert(arr_unmodified[1]==2, "assertion arr_unmodified[1]==2");

  (*arr_modified) += 1;
  // arr_modified[1] = 3;

  __CPROVER_assert(*arr_modified == 2, "assertion *arr_modified == 2");
  // __CPROVER_assert(arr_modified[1]==3, "assertion arr_modified[1]==3");

  return arr_modified;
}
