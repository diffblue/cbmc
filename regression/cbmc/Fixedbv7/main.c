#include <assert.h>

typedef __CPROVER_fixedbv[32][16] fbvt;

int main()
{
  fbvt f;

  // addition
  assert((fbvt)100.0+10==110);
  assert(0+f==f);
  assert(f+0==f);
  assert(100+(fbvt)0.5==(fbvt)100.5);
  assert((fbvt)0.0+(fbvt)0.0+f==f);

  // subtraction
  assert((fbvt)100.0-10==90);
  assert(0-f==-f);
  assert(f-0==f);
  assert(100-(fbvt)0.5==(fbvt)99.5);
  assert((fbvt)0.0-(fbvt)0.0-f==-f);

  // unary minus
  assert(-(fbvt)(-100.0)==100);
  assert(-(1-(fbvt)2.0)==1);
  assert(-(-f)==f);

  // multiplication
  assert((fbvt)100.0*10==1000);
  assert(0*f==0);
  assert(f*0==0);
  assert(100*(fbvt)0.5==50);
  assert(f*1==f);
  assert(1*f==f);
  assert((fbvt)1.0*(fbvt)1.0*f==f);

  // division
  assert((fbvt)100.0/(fbvt)1.0==100);
  assert((fbvt)100.1/(fbvt)1.0==(fbvt)100.1);
  assert((fbvt)100.0/(fbvt)2.0==50);
  assert((fbvt)100.0/(fbvt)0.5==200);
  assert(0/(fbvt)1.0==0);
  assert(f/(fbvt)1.0==f);

  // conversion
  assert(((__CPROVER_fixedbv[40][16])(fbvt)100)==(__CPROVER_fixedbv[40][16])100.0);
  assert(((unsigned int)(fbvt)100.0)==100.0);
  assert(100.0);
  assert(!0.0);
  assert((int)(fbvt)0.5==0);
  assert((int)(fbvt)0.49==0);
  assert((int)(fbvt)-1.5==-1);
  assert((int)(fbvt)-10.49==-10);

  // relations
  assert((fbvt)1.0<(fbvt)2.5);
  assert((fbvt)1.0<=(fbvt)2.5);
  assert((fbvt)1.01<=(fbvt)1.01);
  assert((fbvt)2.5>(fbvt)1.0);
  assert((fbvt)2.5>=(fbvt)1.0);
  assert((fbvt)1.01>=(fbvt)1.01);
  assert(!((fbvt)1.0>=(fbvt)2.5));
  assert(!((fbvt)1.0>(fbvt)2.5));
  assert((fbvt)1.0!=(fbvt)2.5);
}
