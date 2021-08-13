int main(void)
{
  int arr[] = {1, 2, 3};
  int ix;
  if(ix)
  {
    ix = 0;
  }
  else
  {
    ix = 2;
  }
  // ix is between 0 and 2
  // so this is between 1 and 3
  int arr_at_ix = arr[ix];
  int write_ix;
  if(write_ix)
  {
    write_ix = 0;
  }
  else
  {
    write_ix = 1;
  }
  arr[write_ix] = 4;
  int arr_0_after_write = arr[0];
  int arr_1_after_write = arr[1];
  // We can't write to arr[2]
  // because write_ix is between 0 and 1
  // so this should be unchanged
  int arr_2_after_write = arr[2];
  return 0;
}
