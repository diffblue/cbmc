// _Float16 exhaustive verification of IEEE 754 special cases.
// Each assertion corresponds to a proved property.
// (Coq: special case handling in float_utilst::rem)

#include <assert.h>

#if defined(__GNUC__) && __GNUC__ >= 13

_Float16 __CPROVER_fmodf16(_Float16, _Float16);

int main()
{
  _Float16 pos_inf = (_Float16)(1.0 / 0.0);
  _Float16 neg_inf = -pos_inf;
  _Float16 nan_val = pos_inf + neg_inf;
  _Float16 x, y;

  // fmod(±inf, y) = NaN for all y
  __CPROVER_assume(y == y);
  _Float16 r1 = __CPROVER_fmodf16(pos_inf, y);
  assert(r1 != r1);
  _Float16 r2 = __CPROVER_fmodf16(neg_inf, y);
  assert(r2 != r2);

  // fmod(x, ±0) = NaN for all non-NaN x
  __CPROVER_assume(x == x);
  _Float16 r3 = __CPROVER_fmodf16(x, (_Float16)0.0);
  assert(r3 != r3);

  // fmod(NaN, y) = NaN, fmod(x, NaN) = NaN
  _Float16 r5 = __CPROVER_fmodf16(nan_val, (_Float16)1.0);
  assert(r5 != r5);
  _Float16 r6 = __CPROVER_fmodf16((_Float16)1.0, nan_val);
  assert(r6 != r6);

  // fmod(x, ±inf) = x for finite x
  __CPROVER_assume(x != pos_inf && x != neg_inf);
  assert(__CPROVER_fmodf16(x, pos_inf) == x);
  assert(__CPROVER_fmodf16(x, neg_inf) == x);
}

#else
int main()
{
}
#endif
