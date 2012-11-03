int x, y;

void f()
{
  int *px=&x;

  x=1;
  px++;
  
  y=*px;
}
