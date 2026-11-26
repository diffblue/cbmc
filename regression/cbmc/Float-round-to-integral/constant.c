// Constant inputs, which the simplifier folds using ieee_floatt.

#include <assert.h>

int main()
{
  typedef __CPROVER_floatbv[28][23] e4_floatt;
  assert(__CPROVER_round_to_integralf((e4_floatt)2.5f, 0) == 2);
  assert(__CPROVER_round_to_integralf((e4_floatt)2.5f, 4) == 3);
  assert(__CPROVER_round_to_integralf((e4_floatt)-0x1.fffffep7f, 3) == -255);
  assert(
    __CPROVER_round_to_integralf((e4_floatt)0x1.fffffep7f, 0) ==
    (e4_floatt)(1.0f / 0.0f));

  typedef __CPROVER_floatbv[5][2] e2_floatt;
  assert(__CPROVER_round_to_integralf((e2_floatt)0.5f, 0) == 0);
  assert(__CPROVER_round_to_integralf((e2_floatt)1.5f, 0) == 2);
  assert(__CPROVER_round_to_integralf((e2_floatt)0.25f, 2) == 1);

  assert(__CPROVER_round_to_integralf(2.5f, 0) == 2.0f);
  assert(__CPROVER_round_to_integralf(-2.5f, 4) == -3.0f);
  assert(__CPROVER_round_to_integrald(0x1.fffffffffffffp51, 2) == 0x1p52);
  return 0;
}
