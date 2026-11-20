typedef __CPROVER_size_t size_t;

// Even when a backing array is created via rw_ok, CBMC still checks that each
// dereference is within the bounds of that array: accessing a[3] when only
// 3 * sizeof(*a) bytes (indices 0..2) were assumed valid must be reported.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  size_t n = 3;
  unsigned int *a;
  __CPROVER_assume(__CPROVER_rw_ok(a, n * sizeof(*a)));
  a[3] = 0; // out of bounds: valid indices are 0..2
  return 0;
}
