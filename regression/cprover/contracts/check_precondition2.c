void callee(int parameter)
  // clang-format off
  __CPROVER_requires(parameter >= 10)
// clang-format on
{
}

void caller(int some_value)
  // clang-format off
  __CPROVER_requires(1)
// clang-format on
{
  if(some_value >= 10)
    callee(some_value); // precondition passes
}
