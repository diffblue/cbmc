// An rw_ok whose constant size is smaller than one element cannot be backed by
// a typed object. CBMC warns that the assumption has no effect and creates no
// backing object, so the subsequent dereference still fails pointer checks --
// the assumption is soundly discarded rather than silently granting access.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  int *p;
  __CPROVER_assume(__CPROVER_rw_ok(p, 1)); // 1 < sizeof(int)
  int x = *p;
  __CPROVER_assert(x == x, "deref still checked");
  return 0;
}
