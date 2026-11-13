struct S
{
  int data[4];
  int x;
};

struct S nondet_S(void);

int main()
{
  struct S s = nondet_S();
  int arr[4];
  arr[0] = s.data[0];
  arr[1] = s.data[1];
  __CPROVER_assert(arr[0] == arr[1], "check");
  return 0;
}
