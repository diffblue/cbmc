void assigns_single(int a[], int len) __CPROVER_assigns(a)
{
}

void assigns_range(int a[], int len) __CPROVER_assigns(a)
{
}

void assigns_big_range(int a[], int len) __CPROVER_assigns(a)
{
  assigns_single(a, len);
  assigns_range(a, len);
}

int main()
{
  int arr[10];
  assigns_big_range(arr, 10);

  return 0;
}
