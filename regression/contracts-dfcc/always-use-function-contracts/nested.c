/// \file
/// Follow retained bodies but stop at contract replacements.

int private_helper(void)
{
  return 7;
}

int unused(void)
{
  return private_helper();
}

int callee(void)
  // clang-format off
  __CPROVER_ensures(__CPROVER_return_value == 7)
// clang-format on
{
  return private_helper();
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
