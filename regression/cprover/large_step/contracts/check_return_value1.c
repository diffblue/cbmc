int my_function1(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value >= 0) // passes
// clang-format on
{
  return 10;
}

int my_function2(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value >= 0) // fails
// clang-format on
{
  return -10;
}
