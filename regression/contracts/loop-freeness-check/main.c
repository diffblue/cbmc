int foo(int *arr)
  // clang-format off
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(arr))
// clang-format off
{
  for(int i = 0; i < 10; i++)
    arr[i] = i;

  return 0;
}

int main()
{
  int arr[10];
  foo(arr);
}
