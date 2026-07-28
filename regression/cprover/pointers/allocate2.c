// Soundness companion: an out-of-bounds access to an __CPROVER_allocate'd
// object must still be refuted (the allocate rewrite must not mask it).
void *__CPROVER_allocate(__CPROVER_size_t, int);

int *p;

int main()
{
  p = __CPROVER_allocate(sizeof(int), 0);
  p[5] = 123;
  __CPROVER_assert(p[5] == 123, "property 1");
  return 0;
}
