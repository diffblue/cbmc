void func(int a)
{
  __CPROVER_precondition(a > 10, "Argument should be larger than 10.");
}

int main()
{
  int a = 10;

  func(a);

  return 0;
}
