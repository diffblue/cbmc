int foo (int iX, int iY)
{
  return iX + iY;
}

int main(void)
{
  int iN = 2 + 1;
  if (iN == 4)

  // assert() is platform-dependent and changes set of coverage goals
    __CPROVER_assert(foo(5,3)==8, "");
}
