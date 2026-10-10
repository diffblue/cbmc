int global;

void my_function1(int parameter)
  // clang-format off
  __CPROVER_ensures(global >= 0) // passes
// clang-format on
{
  global = 10;
}

void my_function2(int parameter)
  // clang-format off
  __CPROVER_ensures(global >= 0) // fails
// clang-format on
{
}
