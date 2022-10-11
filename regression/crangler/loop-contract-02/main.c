int foo(int *arr, int size)
{
  arr[0] = 0;
  arr[size - 1] = 0;
  for(int i = 0; i < 2; i++)
  {
    arr[i] = 0;
  }

  int i = 0;
  while(i < 2)
  {
    arr[i] = 0;
    i++;
  }

  return size < 10 ? 0 : arr[5];
}

int main()
{
  int arr[10];
  int retval = foo(arr, 10);
  __CPROVER_assert(retval == arr[5], "should succeed");
  return 0;
}
