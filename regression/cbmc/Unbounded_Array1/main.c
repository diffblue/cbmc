int main()
{
  unsigned int n = __VERIFIER_nondet_int(),
               i = __VERIFIER_nondet_unsigned_int(),
               j = __VERIFIER_nondet_unsigned_int(), ai, aj;
  int a[n];

  __CPROVER_assume(n > 10 && n < 10000000);

  __CPROVER_assume(i < n);
  __CPROVER_assume(j < n);

  ai = a[i];
  aj = a[j];

  assert(ai == aj || i != j);
}
