int calls;

int *f(int *p)
{
  ++calls;
  return p;
}

int g(void)
{
  ++calls;
  return 1;
}

int main()
{
  int m = 0;
#ifdef __GNUC__
  // the operands are evaluated exactly once, before the statement
  __asm__ volatile("mfence" : "=m"(*f(&m)) : "r"(g()));
#else
  calls = 2;
#endif
  __CPROVER_assert(calls == 2, "operands are evaluated");
  return 0;
}
