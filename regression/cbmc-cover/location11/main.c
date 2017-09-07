int myfunc(int x, int y)
{
  int z = x + y;
  return z;
}

int main(void)
{
  _Bool x=0, y;
  if(x)
    myfunc(2, 3);
  else
    y=1;

  if(y)
    y=0;
  else 
    __CPROVER_assume(0);

  return 0;
}
