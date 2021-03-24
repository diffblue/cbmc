/* clang-format off */
void assign_out_under(int a[], int len) __CPROVER_assigns(a[2 .. 5])
/* clang-format on */
{
  a[1] = 5;
}

int main()
{
  int arr[10];
  assign_out_under(arr, 10);

  return 0;
}
