void assigns_ptr(int *x)
{
  *x = 200;
}

void uses_assigns(int a[], int i, int len)
  // clang-format off
 __CPROVER_requires(0 <= i && i < len)
  __CPROVER_assigns(*(&a[i]))
// clang-format on
{
  int *ptr = &(a[i]);
  assigns_ptr(ptr);
}

int main()
{
  int arr[10];
  int i;
  __CPROVER_assume(0 <= i && i < 10);
  uses_assigns(arr, i, 10);
  return 0;
}
