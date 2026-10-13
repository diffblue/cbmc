int main()
{
  unsigned n;
  __CPROVER_assume(n > 0 && n < 8);
  int a[n];
  __CPROVER_array_set(a, 0);
  unsigned i;
  __CPROVER_assume(i < n);
  __CPROVER_assert(a[i] == 0, "zero");
  return 0;
}
