void foo(int *in1, int *in2)
  // clang-format off
  __CPROVER_requires(
    __CPROVER_is_fresh(in1, sizeof(int)) &&
    __CPROVER_is_fresh(in2, sizeof(int)) &&
    *in1 == 0 &&
    *in2 == 0)
// clang-format on
{
  __CPROVER_assert(__CPROVER_rw_ok(in1, sizeof(int)), "in1 is rw_ok");
  __CPROVER_assert(__CPROVER_rw_ok(in2, sizeof(int)), "in2 is rw_ok");
  __CPROVER_assert(
    !__CPROVER_same_object(in1, in2), "in1 and in2 do not alias");
  __CPROVER_assert(*in1 == 0, "in1 is zero");
  __CPROVER_assert(*in2 == 0, "in2 is zero");
}

int main()
{
  int *in1;
  int *in2;
  foo(in1, in2);
  return 0;
}
