int main()
{
  _Static_assert(!__CPROVER_overflow_plus(1, 2), "");
  _Static_assert(__CPROVER_overflow_minus(1U, 2U), "");
  _Static_assert(__CPROVER_overflow_minus(0U, 2U), "");
  _Static_assert(!__CPROVER_overflow_mult(1U, 2U), "");
  _Static_assert(!__CPROVER_overflow_shl(1, 2), "");
  _Static_assert(!__CPROVER_overflow_unary_minus(1), "");
  _Static_assert(__CPROVER_overflow_unary_minus(1U), "");
}
