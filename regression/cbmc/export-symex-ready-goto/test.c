int main(int argc, char **argv)
{
  int arr[] = {0, 1, 2, 3, 4};
  __CPROVER_assert(arr[0] == 1, "expected failure: 0 != 1");
  return 0;
}
