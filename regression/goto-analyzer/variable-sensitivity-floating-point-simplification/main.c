#include <assert.h>

int main(void)
{
  const float one = 1.0f;
  // Check that rounding mode affects behavior

  // default rounding mode towards nearest
  float big_0_1 = one / 10.0f;
  __CPROVER_rounding_mode = 1; // round to -∞
  float small_0_1 = one / 10.0f;
  assert(small_0_1 < big_0_1);

  // Check that exact operations still work with unknown rounding mode
  int some_condition;
  if(some_condition)
  {
    __CPROVER_rounding_mode = 3;
  }
  // rounding mode is TOP now

  // regardless of rounding mode,
  // 1/10 is definitely smaller than 0.2
  assert(one / 10.0f < 0.2f);

  // This is unknown because
  // we don't know the value of one_tenth_ish
  // (could be slightly less or slightly more than 0.1)
  // This is contrast to above, where we didn't need
  // to know the exact value of one/10.0f, just
  // that it is less than 0.2f
  float one_tenth_ish = one / 10.0f;
  assert(one_tenth_ish < 0.2f);

  // regardless of rounding mode,
  // 10/5 is still 2
  float five = 5.0f;
  assert(10.0f / five == 2.0f);

  return 0;
}
