int func(int a)
{
  int b = a*2;
  return b;

  if (b < 10)
  {
    b += 10;
  }

  // assert() is platform-dependent and changes set of coverage goals
  __CPROVER_assert(0, "");

  return b;
}

int main(void)
{
  func(2);
}
