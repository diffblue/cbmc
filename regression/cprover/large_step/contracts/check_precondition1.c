void my_function(int parameter)
  // clang-format off
  __CPROVER_requires(parameter >= 10)
// clang-format on
{
}

int main()
{
  my_function(-123); // fails
  my_function(123);  // passes
  return 0;
}
