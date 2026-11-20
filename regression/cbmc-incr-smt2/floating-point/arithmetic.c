float nondet_float(void);

int main(void)
{
  float a = nondet_float(), b = nondet_float();
  __CPROVER_assume(a == 2.0f && b == 4.0f);
  __CPROVER_assert(a * b == 8.0f, "multiplication");
  __CPROVER_assert(a / b == 0.5f, "division");
  __CPROVER_assert(a + b == 6.0f, "addition");
  __CPROVER_assert(a - b == -2.0f, "subtraction");
  __CPROVER_assert(a / b == 0.25f, "expected to fail");
  return 0;
}
