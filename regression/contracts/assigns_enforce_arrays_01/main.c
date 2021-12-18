void f1(int a[], int len) __CPROVER_assigns()
{
  int b[10];
  a = b;
  int *indr = a + 2;
  *indr = 5;
  a[5] = 2;
}

int main()
{
  int arr[10];
  f1(arr, 10);

  return 0;
}
