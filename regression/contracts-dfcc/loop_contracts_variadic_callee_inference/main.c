// The functions to instrument are ordered by when their names were first
// interned. The variadic function is called printf, which is a predefined
// identifier (ID_printf in util/irep_ids.def), so that it is instrumented
// before loop_fn.
int printf(const char *fmt, ...)
{
  (void)fmt;
  return 0;
}

void loop_fn(unsigned n)
{
  unsigned short v;
  unsigned i = 0;
  while(i < n)
    // clang-format off
    __CPROVER_loop_invariant(i <= n)
    __CPROVER_decreases(n - i)
    // clang-format on
    {
      printf("%d", v);
      i++;
    }
}

int main(void)
{
  unsigned n;
  loop_fn(n);
  return 0;
}
