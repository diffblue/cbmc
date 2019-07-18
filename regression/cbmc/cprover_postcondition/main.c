int func(int a)
{
  __CPROVER_precondition(a > 10, "Argument should be larger than 10");
  int rval = a - 10;
  __CPROVER_postcondition(rval > 1, "Return value should be positive");
  return rval;
}

int main()
{
  int a = 11;
  int rval = func(a);
  return 0;
}
