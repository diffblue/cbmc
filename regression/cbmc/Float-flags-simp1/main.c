#include <math.h>
#include <float.h>
#include <assert.h>

int main()
{
  double d;

  // first check constants
  
  #ifndef _MSC_VER
  assert(isnormal(FLT_MAX));
  assert(isinf(HUGE_VAL));
  assert(isinf(HUGE_VALF));
//  assert(isinf(HUGE_VALL));
  assert(isinf(INFINITY));
  assert(isnan(NAN));
  #endif

  // check +
  #ifndef _MSC_VER
  assert(isinf(INFINITY+INFINITY));
  #endif
  assert(isnan(-INFINITY+INFINITY));
  assert(INFINITY+INFINITY>0);
  #ifndef _MSC_VER
  assert(isnan(NAN+d));
  assert(isnan(NAN+INFINITY));
  #endif

  // check -
  assert(isnan(INFINITY-INFINITY));
  #ifndef _MSC_VER
  assert(isinf(-INFINITY-INFINITY));
  #endif
  assert(-INFINITY-INFINITY<0);
  #ifndef _MSC_VER
  assert(isnan(NAN-d));
  assert(isnan(NAN-INFINITY));
  #endif

  // check *
  #ifndef _MSC_VER
  assert(isinf(INFINITY*INFINITY));
  assert(isinf(-INFINITY*INFINITY));
  #endif
  assert(INFINITY*INFINITY>0);
  assert(-INFINITY*INFINITY<0);
  #ifndef _MSC_VER
  assert(isnan(NAN*d));
  assert(isnan(NAN*INFINITY));
  #endif
  assert(isnan(INFINITY*0));
  assert(signbit(1.0*-0.0));
  assert(!signbit(1.0*0.0));

  // check /
  assert(isnan(INFINITY/INFINITY));
  assert(isnan(-INFINITY/INFINITY));
  #ifndef _MSC_VER
  assert(isinf(INFINITY/0));
  #endif
  assert(0.0/INFINITY==0);
  assert(1.0/INFINITY==0);
  assert(signbit(-1.0/INFINITY));
  assert(signbit(1.0/-INFINITY));
  assert(INFINITY/-2<0);
  #ifndef _MSC_VER
  assert(isinf(1.0/0.0));
  assert(isinf(INFINITY/2));
  #endif
  assert(isnan(0.0/0.0));
  #ifndef _MSC_VER
  assert(isnan(NAN/d));
  assert(isnan(NAN/INFINITY));
  #endif
  assert(signbit(-0.0/1));
}
