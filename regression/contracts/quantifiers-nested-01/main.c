// clang-format off
int f1(int *arr)
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(arr))
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    __CPROVER_forall
    {
      int j;
      (0 <= i && i < 10 && i <= j && j < 10) ==> arr[i] <= arr[j]
    }
  })
// clang-format on
{
  arr[0] = 0;
  arr[1] = 1;
  arr[2] = 2;
  arr[3] = 3;
  arr[4] = 4;
  arr[5] = 5;
  arr[6] = 6;
  arr[7] = 7;
  arr[8] = 8;
  arr[9] = 9;

  return 0;
}

int main()
{
  int arr[10];
  f1(arr);
}
