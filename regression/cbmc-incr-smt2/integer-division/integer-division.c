int main()
{
  // Symbolic operands so the division is not constant-folded away and is
  // actually solved by the SMT back-end.
  __CPROVER_integer a;
  __CPROVER_assume(a > -10 && a < 0); // a in [-9, -1]
  // a / 2 truncates toward zero, so it ranges over [-4, 0]; flooring would
  // reach -5 (for a == -9). This assertion holds iff division truncates.
  __CPROVER_assert(a / 2 >= -4, "negative dividend divides toward zero");

  __CPROVER_integer c;
  __CPROVER_assume(c > 0 && c < 10); // c in [1, 9]
  // c / -2 likewise truncates: range [-4, 0]; flooring would reach -5.
  __CPROVER_assert(c / -2 >= -4, "negative divisor divides toward zero");

  return 0;
}
