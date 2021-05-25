// clang-format off
int f1(int *arr)
__CPROVER_assigns(*arr)
  __CPROVER_ensures(
    __CPROVER_return_value == 0 &&
    __CPROVER_exists {
      int i;
      (0 <= i && i < 10) && arr[i] == i
    }
  )
// clang-format on
{
  for(int i = 0; i < 10; i++)
  {
    arr[i] = i;
  }

  return 0;
}

int main()
{
  int arr[10];
  f1(arr);
}
