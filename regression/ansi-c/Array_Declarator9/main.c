#define C 10

// const in brackets should make the adjusted pointer const
void f_const(int x[const C], int i)
{
  x++; // should be rejected: increment of read-only parameter
  x[i] = 1;
}

int main()
{
  int arr[C];
  f_const(arr, 0);
  return 0;
}
