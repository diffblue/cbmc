int x, y, z;

_Bool f0()
{
  z=1;
  return 0;
}

_Bool f1()
{
  z=1;
  return 1;
}

int main()
{
  z=2;
  x=(f0() || (z==1));
  assert(x);
  
  z=2;
  x=(f0() && (z=3));
  assert(z==1);

  z=2;
  x=(f1() || (z=3));
  assert(z==1);
  
  z=2;
  x=(f1() && (z=3));
  assert(z==3);  
}
