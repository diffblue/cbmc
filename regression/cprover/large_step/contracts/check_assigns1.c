int global;

void my_function1(void)
  // clang-format off
  __CPROVER_assigns(global) // passes
// clang-format on
{
  global = 10;
}

void my_function2(int parameter)
  // clang-format off
  __CPROVER_assigns() // fails
  __CPROVER_ensures(1)
// clang-format on
{
  global = 10;
}

void my_function3(int *pointer)
  // clang-format off
  __CPROVER_requires(__CPROVER_w_ok(pointer))
  __CPROVER_assigns(*pointer) // passes
// clang-format on
{
  *pointer = 10;
}

void my_function4(void)
  // clang-format off
  __CPROVER_assigns() // passes
// clang-format on
{
  int local;
  local = 10;
}
