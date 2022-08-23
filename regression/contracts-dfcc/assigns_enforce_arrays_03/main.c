void assign_out_under(int a[], int len) __CPROVER_assigns()
{
  a[1] = 5;
}

int main()
{
  int arr[10];
  assign_out_under(arr, 10);

  return 0;
}
