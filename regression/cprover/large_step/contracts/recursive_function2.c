int recursive_function()
  __CPROVER_ensures(__CPROVER_return_value == 10) // passes
{
  return recursive_function();
}
