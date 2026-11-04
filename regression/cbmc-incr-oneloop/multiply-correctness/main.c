// Multiplication correctness tests
// Tests both SAT (factors exist) and UNSAT (prime) cases,
// narrow and wide multiplication, and algebraic properties.

void test_factor_narrow(void)
{
  // 3 * 5 = 15, factors exist
  __CPROVER_bitvector[8] p, q;
  __CPROVER_assume(p > 1 && q > 1);
  __CPROVER_assert(p * q != 15, "narrow factor: 15 = 3*5");
}

void test_prime_narrow(void)
{
  // 13 is prime, no factors
  __CPROVER_bitvector[8] p, q;
  __CPROVER_assume(p > 1 && q > 1);
  __CPROVER_bitvector[16] wp = p, wq = q;
  __CPROVER_assert(wp * wq != 13, "narrow prime: 13");
}

void test_factor_wide(void)
{
  // 15 * 69905 = 1048575, factors exist (wide multiplication)
  __CPROVER_bitvector[20] p, q;
  __CPROVER_assume(p > 1 && q > 1);
  __CPROVER_bitvector[40] wp = p, wq = q;
  __CPROVER_assert(wp * wq != 1048575ULL, "wide factor: 1048575 = 15*69905");
}

void test_prime_wide(void)
{
  // 1048573 is prime, no factors (wide multiplication)
  __CPROVER_bitvector[20] p, q;
  __CPROVER_assume(p > 1 && q > 1);
  __CPROVER_bitvector[40] wp = p, wq = q;
  __CPROVER_assert(wp * wq != 1048573ULL, "wide prime: 1048573");
}

void test_commutativity(void)
{
  __CPROVER_bitvector[8] a, b;
  __CPROVER_bitvector[8] c = a * b;
  __CPROVER_bitvector[8] d = b * a;
  __CPROVER_assert(c == d, "commutativity");
}

void test_not_equal(void)
{
  // a*b != a+b in general
  __CPROVER_bitvector[8] a, b;
  __CPROVER_assert(a * b == a + b, "mul != add");
}

int main(void)
{
  test_factor_narrow();
  test_prime_narrow();
  test_factor_wide();
  test_prime_wide();
  test_commutativity();
  test_not_equal();
}
