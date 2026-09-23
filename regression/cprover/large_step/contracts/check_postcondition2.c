int global;

void my_function1(int parameter)
  // clang-format off
  __CPROVER_ensures(global == parameter) // passes
  __CPROVER_assigns(global)
// clang-format on
{
  parameter++;
  global = parameter;
}

void my_function2(int parameter)
  // clang-format off
  __CPROVER_ensures(global == parameter) // fails
  __CPROVER_assigns(global)
// clang-format on
{
  global = parameter;
  parameter++;
}
