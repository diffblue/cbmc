int a[10];

int main(void)
{
  unsigned i, j;
  __CPROVER_assume(i < 10 && j < 10);
  int *p = &a[i];
  int *q = &a[j];
  // The difference of two pointers into the same array is always
  // representable in ptrdiff_t; no signed overflow is possible.
  long d = q - p;
  __CPROVER_assert(d == (long)j - (long)i, "difference value");
  return 0;
}
