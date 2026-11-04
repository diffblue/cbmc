int main()
{
  // The body does not hold for every array (e.g. a[0] != a[1]), so
  // verification must fail. This confirms the array-typed quantifier body is
  // genuinely evaluated rather than the quantifier being silently dropped.
  // clang-format off
  __CPROVER_assert(
    __CPROVER_forall { int a[3]; a[0] == a[1] },
    "does not hold for every array-typed bound variable");
  // clang-format on

  return 0;
}
