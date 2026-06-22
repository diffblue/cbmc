// Known limitation: __CPROVER_allocate(size, 1) is the calloc lowering and
// requests zero-initialised memory, but the cprover state encoder drops the
// zero-init operand and models nondeterministic contents (like malloc), so a
// read of the freshly-allocated memory cannot be proven to be 0.  Documented
// as a KNOWNBUG; promote to CORE if/when zeroing is modelled.
void *__CPROVER_allocate(__CPROVER_size_t, int);

int *p;

int main()
{
  p = __CPROVER_allocate(sizeof(int), 1); // calloc-style: zero-initialised
  __CPROVER_assert(p[0] == 0, "property 1");
  return 0;
}
