int main()
{
  int a[2] = {0};
  int b[2] = {0};
  __CPROVER_assert(__CPROVER_array_equal(a, b), "equal");
}
