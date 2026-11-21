void my_function(unsigned parameter)
  // clang-format off
  __CPROVER_requires(1)
// clang-format on
{
  for(unsigned counter = 0; counter != 100; counter++)
  {
    __CPROVER_assert(parameter == __CPROVER_old(parameter), "property 1");
  }

  __CPROVER_assert(parameter == __CPROVER_old(parameter), "property 2");
}
