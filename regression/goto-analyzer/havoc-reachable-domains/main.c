int global;

int main()
{
  global = 1;
  int local = 2;
  int *p = &local;
  int unaddressed = 3;
#ifdef __GNUC__
  asm volatile("cli" ::: "memory");
#else
  __asm { cli }
#endif
  __CPROVER_assert(global == 1, "global");                     // may change
  __CPROVER_assert(local == 2, "address-taken local");         // may change
  __CPROVER_assert(unaddressed == 3, "local without address"); // unchanged
  return 0;
}
