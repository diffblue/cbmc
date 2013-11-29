int main(void)
{
  int x, y;
  
  x=100;
  
  y=x/=2;
  assert(x==50);
  
  y=x*=3;
  assert(x==150);

  y=x<<=1;
  assert(x==300);

  y=x>>=1;
  assert(x==150);

  y=x+=x;
  assert(x==300);

  y=x^=1;
  assert(x==301);

  y=x-=x;
  assert(x==0);

  y=x|=1;
  assert(x==1);

  y=x&=2;
  assert(x==0);

  return 0;
}
