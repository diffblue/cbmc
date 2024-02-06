int foo()
{
  return 1;
}

int main()
{
  if(foo())
    goto out;

  return 1;

out:
  __CPROVER_assert(0, "false");
  return 0;
}
