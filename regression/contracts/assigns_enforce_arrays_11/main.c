void assigns_single(int a[], int len) __CPROVER_assigns(a[7])
{
}

/* clang-format off */
void assigns_range(int a[], int len) __CPROVER_assigns(a[2 .. 5])
/* clang-format on */
{
}

/* clang-format off */
void assigns_big_range(int a[], int len) __CPROVER_assigns(a[2 .. 7])
/* clang-format on */
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
