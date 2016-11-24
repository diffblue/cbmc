int main()
{
  // constants
  assert(1.0!=2.0);
  assert(1.0==1.0);
  assert(1.0<2.0);
  assert(!(-1.0<-2.0));
  assert(2.0>1.0);
  assert(!(-2.0>-1.0));
  assert(!(2.0<2.0));
  assert(!(-2.0<-2.0));
  assert(!(2.0>2.0));
  assert(!(-2.0>-2.0));
  assert(2.0<=2.0);
  assert(-2.0<=-2.0);
  assert(2.0>=2.0);
  assert(-2.0>=-2.0);
  assert(1.0<=2.0);
  assert(!(-1.0<=-2.0));
  assert(2.0>=1.0);
  assert(!(-2.0>=-1.0));  
  
  // variables
  float a, b, _a=a, _b=b;
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
