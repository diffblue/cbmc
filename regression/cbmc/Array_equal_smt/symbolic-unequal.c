unsigned nondet_unsigned();
int main()
{
  unsigned n = nondet_unsigned();
  __CPROVER_assume(n > 0 && n <= 2);
  typedef int T[n];
  T a, b;
  __CPROVER_assume(a[0] == b[0]);
  __CPROVER_assert(__CPROVER_equal(a, b), "a[1] and b[1] may differ");
  __CPROVER_assert(!__CPROVER_equal(a, b), "a and b may be equal");
  return 0;
}
