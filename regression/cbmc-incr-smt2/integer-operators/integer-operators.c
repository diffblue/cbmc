int main()
{
  __CPROVER_integer a, b;
  __CPROVER_assume(a > 100);
  __CPROVER_assume(b <= 100);

  // subtraction combined with a comparison
  __CPROVER_assert(a - b > 0, "a - b > 0");
  // unary minus
  __CPROVER_assert(-a < 0, "-a < 0");
  // the remaining relational operators
  __CPROVER_assert(b <= a, "b <= a");
  __CPROVER_assert(a >= b, "a >= b");

  return 0;
}
