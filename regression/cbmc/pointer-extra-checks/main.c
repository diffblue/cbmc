int main()
{
  {
    int *p = 0x0;

    // Since local_bitvector_analysis can tell that p is NULL, this should
    // generate only a NULL check, and not any of the other pointer checks.
    *p = 1;
  }

  {
    int i;
    int *q = &i;

    // This should only generate a not-dead check and a bounds-check.
    *q = 2;
  }

  {
    int *r = __CPROVER_allocate(sizeof(int), 1);

    // This should generate a not-deallocated check and a bounds-check.
    *r = 5;
  }

  {
    int *s;

    // This should generate an invalid pointer check (labelled uninitialized).
    *s = 14;
  }

  return 0;
}
