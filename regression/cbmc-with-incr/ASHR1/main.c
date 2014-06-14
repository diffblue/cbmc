int main()
{
  int x=-4, y;
  // should succeed
  y=x>>1;
  x>>=1;
  assert(x==-2);
  assert(y==-2);
  
  // should also work with mixed types
  assert(((-2)>>1u)==-1);

  // more arithmetic shifts for negative numbers  
  x=-1;
  x=x>>1;  
  assert(x==-1);
  
  x=-10;
  x=x>>10;
  assert(x==-1);  
}
