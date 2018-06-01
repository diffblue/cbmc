int missing_return(int x)
{
  if(x)
    return x;

  // missing return statement
}

int missing_return_value(int x)
{
  if(x)
    return x;

  return; // missing value
}

int main()
{
  __CPROVER_assert(missing_return(0) == 0, "expected to fail");
  __CPROVER_assert(missing_return_value(0) == 0, "expected to fail");

  return 0;
}
