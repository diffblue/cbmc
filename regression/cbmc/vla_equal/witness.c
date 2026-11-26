unsigned nondet_unsigned();

int main()
{
  unsigned n = nondet_unsigned();
  typedef int T[n];
  T a, b;
  __CPROVER_assume(n == 2);
  __CPROVER_assume(a[0] == b[0] && a[1] == b[1]);
  __CPROVER_assert(__CPROVER_equal(a, b), "equal");

  return 0;
}
