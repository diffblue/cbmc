int main()
{
  int a;
  int *p = &a;
  int *q = &a;

  __CPROVER_assert(
    __CPROVER_POINTER_OFFSET(p) != __CPROVER_POINTER_OFFSET(q),
    "expected failure because offsets should be the same");

  // TODO: Remove comments once pointer arithmetic works:

  // *q = p + 2;

  // __CPROVER_assert(__CPROVER_POINTER_OFFSET(p) != __CPROVER_POINTER_OFFSET(q), "expected failure");
}
