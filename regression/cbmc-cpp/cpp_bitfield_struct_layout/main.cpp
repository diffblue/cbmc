// N5008 [class.bit]/1 + [basic.align]/1: a class with bit-fields is laid out
// with the bit-fields packed into and padded out to whole allocation units, so
// it has its ABI size and any member read is in bounds.
//
// Regression: the C++ front-end did not apply the bit-field padding pass, so a
// bit-field-only struct had object size 0; reading a bit-field member through a
// pointer/reference tripped a spurious "pointer outside object bounds" check
// (and sizeof was wrong).  The front-end now runs add_padding() on structs
// containing a bit-field, matching the C front-end.
struct M
{
  unsigned b : 3;
};
static int read_ref(const M &m)
{
  return m.b;
}
int main()
{
  __CPROVER_assert(sizeof(M) == 4, "bit-field-only struct has its ABI size");
  M m;
  m.b = 5;
  __CPROVER_assert(read_ref(m) == 5, "read bit-field through reference (in bounds)");
  return 0;
}
