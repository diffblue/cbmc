void assigns_single(int a[], int len)
{
  int i;
  __CPROVER_assume(0 <= i && i < len);
  a[i] = 0;
}

void uses_assigns(int a[], int len)
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(a))
{
  assigns_single(a, len);
}

int main()
{
  int arr[10];
  uses_assigns(arr, 10);

  return 0;
}
