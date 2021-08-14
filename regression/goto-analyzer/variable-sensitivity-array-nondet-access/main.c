int main(void)
{
  int arr[] = {1, 2, 3, 4, 5};
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
    write_ix = 4;
  }
  arr[write_ix] = 99;
  int arr_0_after_write = arr[0];
  int arr_1_after_write = arr[1];
  int arr_2_after_write = arr[2];
  int arr_3_after_write = arr[3];
  int arr_4_after_write = arr[4];
  return 0;
}
