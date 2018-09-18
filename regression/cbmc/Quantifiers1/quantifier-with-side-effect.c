int func()
{
  return 1;
}

int main()
{
  // clang-format off
  // no side effects!
  assert(__CPROVER_forall { int i; func() });
  // clang-format on

  return 0;
}
