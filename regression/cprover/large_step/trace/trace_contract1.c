int my_function(int parameter)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == 123)
// clang-format on
{
  return parameter;
}
