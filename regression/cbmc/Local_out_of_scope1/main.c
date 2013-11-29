int main()
{
  int *p, *q;
  int x, y, z;
  
  p=&x;
  q=p;
  
  if(z)
  {
    int l;
    q=&l;
  }

  // this should fail, as *p is dead if z is true  
  y=*q;
}
