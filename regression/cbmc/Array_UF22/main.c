int main()
{
  int x;
  int a[2] = {x};
  int b[2] = {x};
  __CPROVER_assert(__CPROVER_array_equal(a, b), "equal");
}
