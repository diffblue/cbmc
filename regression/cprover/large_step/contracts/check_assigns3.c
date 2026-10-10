void my_function1(int *parameter)
  // clang-format off
  __CPROVER_requires(__CPROVER_w_ok(parameter))
  __CPROVER_assigns(*parameter) // passes
  // clang-fromat on
{
  *parameter = 10;
}

void my_function2(int *parameter)
  // clang-format off
  __CPROVER_requires(__CPROVER_w_ok(parameter))
  __CPROVER_assigns() // fails
  // clang-fromat on
{
  *parameter = 10;
}

void my_function3(int *parameter)
  // clang-format off
  __CPROVER_requires(__CPROVER_w_ok(parameter))
  // implicit assigns clause fails
  // clang-fromat on
{
  *parameter = 10;
}
