/* clang-format off */
void f1(int a[], int len) __CPROVER_assigns(a[2 .. 5])
/* clang-format on */
{
  int b[10];
  a = b;
  int *indr = a + 2;
  *indr = 5;
}

int main()
{
  int arr[10];
  f1(arr, 10);

  return 0;
}
