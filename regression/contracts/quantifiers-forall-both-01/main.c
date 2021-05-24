// clang-format off
int f1(int *arr)
  __CPROVER_requires(__CPROVER_forall {
    int i;
    (0 <= i && i < 8) ==> arr[i] == 0
  })
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    (0 <= i && i < 8) ==> arr[i] == 0
  })
// clang-format on
{
  return 0;
}

int main()
{
  int arr[8];
  f1(arr);
}
