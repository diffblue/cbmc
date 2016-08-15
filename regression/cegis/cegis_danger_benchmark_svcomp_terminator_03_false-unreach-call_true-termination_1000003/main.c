int main()
{
  int x;
  int y;

  while(y > 0 && x<1000003)
  {
    x=x+y;
   }

  __CPROVER_assert(y<=0 || (y<0 && x>=1000003), "A");
  return 0;
}
