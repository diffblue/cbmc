int main()
{
  int a[10000];
  unsigned int i, j;
  __CPROVER_assume(i < 10000);
  __CPROVER_assume(j < 10000);

  __CPROVER_array_set(a, 42);

  // Several distinct (nondet) indices into the same array_of-initialised array
  // must all observe the fill value. With the constant-array encoding the
  // array is defined once and every index is constrained, so reads at distinct
  // indices agree.
  __CPROVER_assert(a[i] == 42, "a[i] is the fill value");
  __CPROVER_assert(a[j] == 42, "a[j] is the fill value");
  __CPROVER_assert(a[i] == a[j], "distinct reads agree");
}
