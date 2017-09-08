int foo (int iX, int iY)
{
  return iX + iY;
  __CPROVER_assume(0);
}

int main(void)
{
  foo(5, 3);
}
