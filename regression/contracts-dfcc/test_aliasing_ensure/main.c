int *foo()
  // clang-format off
  __CPROVER_ensures(__CPROVER_is_fresh(__CPROVER_return_value, sizeof(int)))
// clang-format on
{
  int *ret = malloc(sizeof(int));
  __CPROVER_assume(ret);
  return ret;
}

int main()
{
  foo();
  return 0;
}
