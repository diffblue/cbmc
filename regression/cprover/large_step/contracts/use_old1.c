void my_function(int parameter) __CPROVER_requires(1)
{
  int copy = parameter;
  parameter = 456;
  __CPROVER_assert(copy == __CPROVER_old(parameter), "property 1");
}
