int x, y;

void f()
{
  int *px=&x;

  x=1;
  px++;

  // now out of bounds  
  y=*px;
}
