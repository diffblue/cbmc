void assigns_ptr(int *x) __CPROVER_assigns(*x)
{
  *x = 200;
}

void assigns_range(int a[], int len) __CPROVER_assigns(a)
{
  int *ptr = &(a[7]);
  assigns_ptr(ptr);
}

int main()
{
  int arr[10];
  assigns_range(arr, 10);

  return 0;
}
