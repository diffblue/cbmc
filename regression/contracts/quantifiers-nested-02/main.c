// clang-format off
int f1(int *arr)
  __CPROVER_requires(
    __CPROVER_forall {
    int i;
    (0 <= i && i < 9) ==> __CPROVER_forall {
      int j;
      (i <= j && j < 10) ==> arr[i] <= arr[j]
    }}
  )
  __CPROVER_ensures(
    __CPROVER_return_value == 0
  )
// clang-format on
{
  return 0;
}

int main()
{
  int arr[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  f1(arr);
}
