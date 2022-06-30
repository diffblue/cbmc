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

int foo(int *arr, int size)
{
  arr[0] = 0;
  arr[size - 1] = 0;
  return size < 10 ? 0 : arr[5];
}

int main()
{
  int arr[10];
  int retval = foo(arr, 10);
  __CPROVER_assert(retval == arr[5], "should succeed");
  return 0;
}
