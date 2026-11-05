// Functions that DFCC does not instrument (here, through their `__VERIFIER`
// prefix), as verification tools use for the state of their own checks.
// DFCC does not check their writes against a write set, but loops that call
// them must still havoc what they write.
int g = 0;

// Writes through a parameter.
void __VERIFIER_record(int *p)
{
  *p = 2;
}

// Writes a global.
void __VERIFIER_bump(void)
{
  g = 2;
}

// Returns a value.
int __VERIFIER_value(void)
{
  return 3;
}

// Only reads through its parameter.
int __VERIFIER_read(int *p)
{
  int t = *p;
  return t + 1;
}

int main()
{
  int y = 1;
  int r = 0;
  int z = 1;
  int s = 0;

  // The writes happen in a later iteration than the first, so that the
  // assertions after the loops only fail if the loops havoc their targets.
  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      if(i == 5)
        __VERIFIER_record(&y);
    }
  __CPROVER_assert(y == 1, "y written through a parameter");

  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      if(i == 5)
        __VERIFIER_bump();
    }
  __CPROVER_assert(g == 0, "g written as a global");

  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      if(i == 5)
        r = __VERIFIER_value();
    }
  __CPROVER_assert(r == 0, "r assigned the result");

  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      s = __VERIFIER_read(&z);
    }
  __CPROVER_assert(z == 1, "z only read");
  return 0;
}
