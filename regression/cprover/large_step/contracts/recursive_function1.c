int recursive_function(int parameter)
  __CPROVER_requires(parameter >= 0) // passes
{
  if(parameter == 0)
    return 0;
  else
    return recursive_function(parameter - 1) + 1;
}
