typedef __CPROVER_fixedbv[32][16] fbvt;

int main()
{
  // constants
  assert((fbvt)1.0!=(fbvt)2.0);
  assert((fbvt)1.0==(fbvt)1.0);
  assert((fbvt)1.0<(fbvt)2.0);
  assert(!((fbvt)-1.0<(fbvt)-2.0));
  assert((fbvt)2.0>(fbvt)1.0);
  assert(!((fbvt)-2.0>(fbvt)-1.0));
  assert(!((fbvt)2.0<(fbvt)2.0));
  assert(!((fbvt)-2.0<(fbvt)-2.0));
  assert(!((fbvt)2.0>(fbvt)2.0));
  assert(!((fbvt)-2.0>(fbvt)-2.0));
  assert((fbvt)2.0<=(fbvt)2.0);
  assert((fbvt)-2.0<=(fbvt)-2.0);
  assert((fbvt)2.0>=(fbvt)2.0);
  assert((fbvt)-2.0>=(fbvt)-2.0);
  assert((fbvt)1.0<=(fbvt)2.0);
  assert(!((fbvt)-1.0<=(fbvt)-2.0));
  assert((fbvt)2.0>=(fbvt)1.0);
  assert(!((fbvt)-2.0>=(fbvt)-1.0));

  // variables
  fbvt a, b, _a=a, _b=b;
  __CPROVER_assume(a==1 && b==2);

  assert(a!=b);
  assert(a==a);
  assert(a<b);
  assert(!(-a<-b));
  assert(b>a);
  assert(!(-b>-a));
  assert(!(b<b));
  assert(!(-b<-b));
  assert(!(b>b));
  assert(!(-b>-b));
  assert(b<=b);
  assert(-b<=-b);
  assert(b>=b);
  assert(-b>=-b);
  assert(a<=b);
  assert(!(-a<=-b));
  assert(b>=a);
  assert(!(-b>=-a));
}
