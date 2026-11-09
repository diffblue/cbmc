int global;

void my_function1(int parameter)
  __CPROVER_ensures(global == __CPROVER_old(parameter)) // passes
  __CPROVER_assigns(global)
{
  global = parameter;
  parameter++;
}

void my_function2(int parameter)
  __CPROVER_ensures(global == __CPROVER_old(parameter)) // fails
  __CPROVER_assigns(global)
{
  parameter++;
  global = parameter;
}
