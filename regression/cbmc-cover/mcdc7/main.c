int main()
{
  signed x, y;

  y = x*123<0 ? 0 : (x*123>100 ? 100 : x*123 );

  return 1;
}
