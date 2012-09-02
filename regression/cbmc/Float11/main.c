int main()
{
  // relations
  assert(1.0<2.5);
  assert(1.0<=2.5);
  assert(1.01<=1.01);
  assert(2.5>1.0);
  assert(2.5>=1.0);
  assert(1.01>=1.01);
  assert(!(1.0>=2.5));
  assert(!(1.0>2.5));
  assert(1.0!=2.5);

  // same flipped
  assert(-1.0>-2.5);
  assert(-1.0>=-2.5);
  assert(-1.01>=-1.01);
  assert(-2.5<-1.0);
  assert(-2.5<=-1.0);
  assert(-1.01<=-1.01);
  assert(!(-1.0<=-2.5));
  assert(!(-1.0<-2.5));
  assert(-1.0!=-2.5);

  // involving zero
  assert(-1.0<0);
  assert(0.0>-1.0);
  assert(0.0==-0.0);
  assert(0.0>=-0.0);
  assert(1>0);
  assert(0<1);
  assert(1>-0);
  assert(-0<1);
  
  assert(!(0.999f<0.0f));
  assert(!(-0.999f>-0.0f));
  assert(!(0.999f<=0.0f));
  assert(!(-0.999f>=-0.0f));
}
