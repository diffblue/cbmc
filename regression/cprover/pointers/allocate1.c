// Regression test for cprover rewriting __CPROVER_allocate to a state-tied
// allocation, which makes the allocate axioms (live_object, object_size, ...)
// apply to the result. Before the fix the "pointer p safe" checks over the
// allocated object were spuriously refuted; after the fix they are proved
// like for malloc.
void *__CPROVER_allocate(__CPROVER_size_t, int);

int *p;

int main()
{
  p = __CPROVER_allocate(sizeof(int) * 10, 0);
  p[2] = 123;
  __CPROVER_assert(p[2] == 123, "property 1");
  return 0;
}
