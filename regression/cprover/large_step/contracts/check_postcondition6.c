int my_function(int x)
  __CPROVER_ensures(__CPROVER_return_value == __CPROVER_old(x))
{
  for(int i = 0; i < 100; i++)
  {
    // does not modify x
  }

  return x;
}
