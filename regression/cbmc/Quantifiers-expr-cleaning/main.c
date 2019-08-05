int main()
{
  unsigned x, y;

  // assume x and y are zero, but make sure this can't be constant propagated
  __CPROVER_assume(x < 1);
  __CPROVER_assume(y < 1);

  // make value sets produce a derefd_pointer object for ((const char*)p)[i]
  // below
  _Bool nondet;
  int *p = nondet ? &x : &y;

  // clang-format off
  __CPROVER_assert(
    __CPROVER_forall{
      unsigned i; i < sizeof(unsigned) ==> ((const char*)p)[i] == 0},
    "");
  // clang-format on
}
