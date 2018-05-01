void function_a()
{
  __CPROVER_assert(0,"");
}

int main()
{
  function_a();
  return 0;
}
