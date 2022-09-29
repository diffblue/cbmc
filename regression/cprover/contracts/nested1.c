void callee(int *p)
  // clang-format off
  __CPROVER_requires(__CPROVER_rw_ok(p))
// clang-format on
{
}

void caller(int *p)
  // clang-format off
  __CPROVER_requires(__CPROVER_rw_ok(p))
// clang-format on
{
  int i;
  __CPROVER_assert(__CPROVER_rw_ok(p), "property 1");
  callee(&i);
}
