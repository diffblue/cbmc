int main()
{
  unsigned j;
  __CPROVER_assume(j < 2);
  // clang-format off
  __CPROVER_assume(__CPROVER_forall { int i; ({ int a[2] = {i, i}; a[j] == i; }) });
  // clang-format on
  __CPROVER_assert(0, "must fail");
  return 0;
}
