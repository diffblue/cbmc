/// \file
/// Handle a callee without a contract in each replacement mode.

int callee(void)
{
  return 7;
}

int foo(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == 7)
// clang-format on
{
  return callee();
}

int main(void)
{
  foo();
  return 0;
}
