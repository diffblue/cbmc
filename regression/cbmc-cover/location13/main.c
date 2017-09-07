int myfunc(int a, int b)
{
  return a+b;
}

int foo(int iX, int iY)
{
  return iX + iY;
  myfunc(iX, iY);
}

int main(void)
{
  foo(5, 3);
}
