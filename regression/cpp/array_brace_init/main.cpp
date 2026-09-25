struct S
{
  int arr[3];
  S() : arr{1, 2, 3}
  {
  }
};

int main()
{
  S s;
  __CPROVER_assert(s.arr[0] == 1, "arr[0]");
  __CPROVER_assert(s.arr[1] == 2, "arr[1]");
  __CPROVER_assert(s.arr[2] == 3, "arr[2]");
  return 0;
}
