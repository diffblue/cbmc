/// \file
/// Apply default contract replacement to a function pointer's target.

int callee(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value >= 0)
// clang-format on
{
  return 7;
}

int foo(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == 7)
// clang-format on
{
  int (*function_pointer)(void) = callee;
  return function_pointer();
}

int main(void)
{
  foo();
  return 0;
}
