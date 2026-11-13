unsigned nondet_unsigned();

int main()
{
  unsigned n = nondet_unsigned();
  __CPROVER_assume(n > 0 && n <= 2);

  // a and b have types with different size symbols
  int a[n];
  int b[n];
  a[0] = b[0];
  if(n == 2)
    a[1] = b[1];
  __CPROVER_assert(__CPROVER_equal(a, b), "equal");
  __CPROVER_assert(__CPROVER_array_equal(a, b), "array_equal");

  unsigned m = nondet_unsigned();
  __CPROVER_assume(m > 0 && m <= 2);
  int c[m];
  for(unsigned i = 0; i < m; ++i)
    c[i] = a[i % n];
  __CPROVER_assert(m != n || __CPROVER_equal(a, c), "equal if sizes are equal");
  __CPROVER_assert(m == n || !__CPROVER_equal(a, c), "unequal if sizes differ");
  __CPROVER_assert(
    m == n || !__CPROVER_array_equal(a, c), "array_equal: unequal sizes");

  return 0;
}
