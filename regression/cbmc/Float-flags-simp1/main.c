#include <math.h>
#include <assert.h>
#include <values.h>

int main()
{
  double d;

  // first check constants
  assert(isnormal(MAXFLOAT));
  assert(isinf(HUGE_VAL));
  assert(isinf(HUGE_VALF));
//  assert(isinf(HUGE_VALL));
  assert(isinf(INFINITY));
  assert(isnan(NAN));

  // check +
  assert(isinf(INFINITY+INFINITY));
  assert(isnan(-INFINITY+INFINITY));
  assert(INFINITY+INFINITY>0);
  assert(isnan(NAN+d));
  assert(isnan(NAN+INFINITY));

  // check -
  assert(isnan(INFINITY-INFINITY));
  assert(isinf(-INFINITY-INFINITY));
  assert(-INFINITY-INFINITY<0);
  assert(isnan(NAN-d));
  assert(isnan(NAN-INFINITY));

  // check *
  assert(isinf(INFINITY*INFINITY));
  assert(isinf(-INFINITY*INFINITY));
  assert(INFINITY*INFINITY>0);
  assert(-INFINITY*INFINITY<0);
  assert(isnan(NAN*d));
  assert(isnan(NAN*INFINITY));
  assert(isnan(INFINITY*0));
  assert(signbit(1.0*-0.0));
  assert(!signbit(1.0*0.0));

  // check /
  assert(isnan(INFINITY/INFINITY));
  assert(isnan(-INFINITY/INFINITY));
  assert(isinf(INFINITY/0));
  assert(0.0/INFINITY==0);
  assert(1.0/INFINITY==0);
  assert(signbit(-1.0/INFINITY));
  assert(signbit(1.0/-INFINITY));
  assert(isinf(INFINITY/2));
  assert(INFINITY/-2<0);
  assert(isinf(1.0/0.0));
  assert(isnan(0.0/0.0));
  assert(isnan(NAN/d));
  assert(isnan(NAN/INFINITY));
  assert(signbit(-0.0/1));
}
