int foo(int *arr, int size);

#if 0
int foo()
  // clang-format off
__CPROVER_ensures(__CPROVER_return_value != 0)
  // clang-format on
  ;
#endif

void foo(int *arr, int size)
  // clang-format off
__CPROVER_requires(size > 0)
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
