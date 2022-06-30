int foo(int *arr, int size)
  // clang-format off
__CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(
  arr[0], arr[size-1];
  size >= 10: arr[5];
)
__CPROVER_ensures(arr[0] == 0 && arr[size-1] == 0)
__CPROVER_ensures(size >= 10 ==> arr[5] == __CPROVER_return_value)
  // clang-format on
  ;

int main()
{
  int arr[10] = {10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  int retval = foo(arr, 10);
  assert(arr[0] == 0);
  assert(arr[1] == 9);
  assert(arr[2] == 8);
  assert(arr[3] == 7);
  assert(arr[4] == 6);
  assert(arr[5] == retval);
  assert(arr[6] == 4);
  assert(arr[7] == 3);
  assert(arr[8] == 2);
  assert(arr[9] == 0);
  return 0;
}
