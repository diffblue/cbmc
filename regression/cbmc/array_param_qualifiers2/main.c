#define C 10

void f_const(int x[const C], int i)
{
  x[i] = 1;
}

void f_restrict(int x[restrict C], int i)
{
  x[i] = 1;
}

void f_none(int x[C], int i)
{
  x[i] = 1;
}

int main()
{
  int arr[C];
  f_const(arr, 0);
  f_restrict(arr, 0);
  f_none(arr, 0);
  return 0;
}
