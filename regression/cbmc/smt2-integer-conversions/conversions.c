int nondet_int(void);
unsigned nondet_unsigned(void);

int main()
{
  // the values are nondeterministic, so that the conversions are not
  // constant-folded

  // integer to bit-vector: the value modulo 2^width
  __CPROVER_integer i;
  __CPROVER_assume(i > 299 && i < 301);
  __CPROVER_assert((unsigned char)i == 44, "300 as unsigned char");
  __CPROVER_integer m;
  __CPROVER_assume(m > -2 && m < 0);
  __CPROVER_assert((unsigned)m == 0xFFFFFFFFu, "-1 as unsigned");
  __CPROVER_assert((signed char)m == -1, "-1 as signed char");

  // bit-vector to integer
  int x = nondet_int();
  __CPROVER_assume(x == -5);
  __CPROVER_integer j = x;
  __CPROVER_assert(j == -5, "signed");
  int x_min = nondet_int();
  __CPROVER_assume(x_min == -2147483647 - 1);
  __CPROVER_integer j_min = x_min;
  __CPROVER_assert(j_min == -2147483648, "INT_MIN");
  unsigned u = nondet_unsigned();
  __CPROVER_assume(u == 4000000000u);
  __CPROVER_integer k = u;
  __CPROVER_assert(k == 4000000000, "unsigned");

  __CPROVER_assert(j == -6, "fails");
  return 0;
}
