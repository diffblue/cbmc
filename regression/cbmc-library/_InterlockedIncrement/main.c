// Microsoft documents _InterlockedIncrement as incrementing *Addend
// atomically and returning the resulting value.
long _InterlockedIncrement(long volatile *);

int main()
{
  long x = 1;
  long r = _InterlockedIncrement(&x);
  __CPROVER_assert(r == 2 && x == 2, "incremented");
  __CPROVER_assert(x == 1, "WRONG (must FAIL)");
  return 0;
}
