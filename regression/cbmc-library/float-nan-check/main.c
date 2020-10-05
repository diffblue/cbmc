#include <assert.h>
#include <math.h>
#include <stdint.h>

// This test contains a set of operations performed on a floating point numbers
// to verify --nan-check flag. The result of test may change when/if support
// of NaN value propagation checking is supported. Current behaviour of
// --nan-check flag is that it checks whether an arithmetic operation performed
// on a floating point value(s) is generating new not-a-number value. If NaN is
// generated because one of the values is already NaN the assertion is not
// produced.

union container {
  uint32_t u;
  float f;
};

int main(void)
{
  // set special values
  float mynan;
  __CPROVER_assume(isnan(mynan));
  float myinf;
  __CPROVER_assume(isinf(myinf) && myinf > 0.0);
  float myzero;
  __CPROVER_assume(myzero == 0.0f);

  // variables
  union container c = {UINT32_MAX};
  int n;

  // should generate assertion if --nan-check flag will support
  // NaN propagation checking
  float g = (float)(c.u);
  float f = c.f;
  f = c.f + myzero;

  // these operations should generate assertions
  // 0.0 / 0.0 = NaN
  f = myzero / myzero;
  // n / Inf = NaN
  f = n / (myinf);
  // Inf * 0 = NaN
  f = (myinf)*myzero;
  // -Inf + Inf = NaN
  f = (-myinf) + (myinf);
  // Inf + (-Inf) = NaN
  f = (myinf) + (-myinf);
  // Inf - Inf = NaN
  f = (myinf) - (myinf);
  // -Inf - (-Inf) = NaN
  f = (-myinf) - (-myinf);

  // NaN + NaN = NaN
  f = c.f + c.f;
  // NaN / 0.0 = NaN
  f = c.f / myzero;
  // NaN * NaN = NaN
  f = mynan * mynan;
  // NaN + NaN = NaN
  f = mynan + mynan;
  // NaN - NaN = NaN
  f = mynan - mynan;
  // NaN / NaN = NaN
  f = mynan / mynan;
  // NAN + n = NaN
  f = mynan + n;
  // NAN - n = NaN
  f = mynan - n;
  // NAN * n = NaN
  f = mynan * n;
  // NAN / n = NaN
  f = mynan / n;

  return 0;
}
