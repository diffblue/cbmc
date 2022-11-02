int foo(char *arr, unsigned int size)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr &&size > 0: arr[0])
// clang-format on
{
  if(arr && size > 0)
    arr[0] = 1;
}
