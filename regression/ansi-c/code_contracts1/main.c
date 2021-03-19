// clang-format off
int foo()
__CPROVER_ensures(__CPROVER_forall {int i; 1 == 1})
// clang-format on
{
  return 1;
}

// clang-format off
int bar()
__CPROVER_ensures(__CPROVER_forall {int i; 1 == 1} &&
                  __CPROVER_return_value == 1)
// clang-format on
{
  return 1;
}

int main()
{
  foo();
  bar();
}
