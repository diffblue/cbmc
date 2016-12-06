int main()
{
  signed x, y;

  __CPROVER_input("x", x);
  __CPROVER_input("y", y);

  y = x*123<0 ? 0 : (x*123>100 ? 100 : x*123 );

  return 1;
}
