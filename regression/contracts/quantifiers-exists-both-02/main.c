// clang-format off
int f1(int *arr, int *len) __CPROVER_requires(__CPROVER_exists {
  int i;
  (0 <= i && i < len) ==> arr[i] == 0
}) __CPROVER_ensures(__CPROVER_exists {
  int i;
  (0 <= i && i < len) ==> arr[i] == 0
})
// clang-format on
{
  return 0;
}

int main()
{
  int len, arr[8];
  f1(arr, len);
}
