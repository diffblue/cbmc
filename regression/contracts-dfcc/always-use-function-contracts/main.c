/// \file
/// Distinguish a callee's implementation from its weaker contract.

int callee(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value >= 0)
// clang-format on
{
  return 7;
}

int precise_contract(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == 7);
// clang-format on

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
