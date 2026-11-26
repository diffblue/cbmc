int main()
{
  int a[3], b[3];
  __CPROVER_assume(a[0] == b[0] && a[1] == b[1]);
  __CPROVER_assert(__CPROVER_equal(a, b), "a[2] and b[2] may differ");
  __CPROVER_assert(!__CPROVER_equal(a, b), "a[2] and b[2] may be equal");
  return 0;
}
