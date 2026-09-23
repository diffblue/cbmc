void my_function(const int *p)
  // clang-format off
  __CPROVER_requires(__CPROVER_r_ok(p))
  __CPROVER_requires(*p >= 20)
// clang-format on
{
  __CPROVER_assert(*p != 0, "property 1"); // passes
}
