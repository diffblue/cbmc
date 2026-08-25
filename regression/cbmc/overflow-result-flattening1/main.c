// The __builtin_*_overflow family lowers to overflow_result_exprt, a struct
// { value, overflow-* }.  When that struct is flattened into a bit-vector
// (every SMT2 back-end except Z3 and CVC5), the "value" component occupies the
// least-significant bits.  If the flattening and the member accessors disagree
// about the field order, "value" reads back as (result << 1) | overflow_flag
// and the overflow flag reads back as the top bit of the truncated result.
//
// None of the assertions below can fail.  The results are held in globals so
// that no pointer checks are generated for the &-operands.

unsigned int uprod, usum;
signed int sprod, ssum, sdiff;

int main(void)
{
  unsigned int ua, ub;
  __CPROVER_assume(ua < 4);
  __CPROVER_assume(ub < 4);

  int uprod_overflow = __builtin_mul_overflow(ua, ub, &uprod);
  __CPROVER_assert(!uprod_overflow, "small unsigned product does not overflow");
  __CPROVER_assert(uprod < 16, "small unsigned product is small");

  int usum_overflow = __builtin_add_overflow(ua, ub, &usum);
  __CPROVER_assert(!usum_overflow, "small unsigned sum does not overflow");
  __CPROVER_assert(usum < 8, "small unsigned sum is small");

  signed int sa, sb;
  __CPROVER_assume(sa > -4 && sa < 4);
  __CPROVER_assume(sb > -4 && sb < 4);

  int sprod_overflow = __builtin_mul_overflow(sa, sb, &sprod);
  __CPROVER_assert(!sprod_overflow, "small signed product does not overflow");
  __CPROVER_assert(sprod > -16 && sprod < 16, "small signed product is small");

  int ssum_overflow = __builtin_add_overflow(sa, sb, &ssum);
  __CPROVER_assert(!ssum_overflow, "small signed sum does not overflow");
  __CPROVER_assert(ssum > -8 && ssum < 8, "small signed sum is small");

  int sdiff_overflow = __builtin_sub_overflow(sa, sb, &sdiff);
  __CPROVER_assert(
    !sdiff_overflow, "small signed difference does not overflow");
  __CPROVER_assert(sdiff > -8 && sdiff < 8, "small signed difference is small");

  return 0;
}
