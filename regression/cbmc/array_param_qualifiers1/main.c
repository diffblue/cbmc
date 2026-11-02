#define C 10

// With const qualifier, x cannot be modified but array elements can
void f_const(int x[const C], int i)
{
  x[i] = x[i] + 1;
}

// Without qualifiers, x can be modified
void f_none(int x[C], int i)
{
  x++;
  x[i] = x[i] + 1;
}

int main()
{
  int arr[C] = {0};
  f_const(arr, 0);
  f_none(arr, 0);
  __CPROVER_assert(arr[0] == 1, "arr[0] incremented by f_const");
  return 0;
}
