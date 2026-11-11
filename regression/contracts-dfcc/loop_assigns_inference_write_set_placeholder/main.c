// The functions to instrument are ordered by when their names were first
// interned. printf is a predefined identifier (ID_printf in
// util/irep_ids.def), so that it is instrumented, and gets its write set
// parameter, before the loop assigns of loop_fn are inferred.
int a;

int printf(int *p, ...)
{
  *p = 1;
  return 0;
}

void loop_fn(unsigned n)
{
  unsigned i = 0;
  while(i < n)
    // clang-format off
    __CPROVER_loop_invariant(i <= n)
    __CPROVER_decreases(n - i)
    // clang-format on
    {
      printf(&a, 0);
      i++;
    }
}

int main(void)
{
  unsigned n;
  loop_fn(n);
  return 0;
}
