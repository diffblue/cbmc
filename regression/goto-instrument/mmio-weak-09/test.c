volatile int reg;

int landed;

void observe(int value)
{
  landed = 1;
}

int main()
{
  reg = 1;
  // ARM data memory barrier (ordering only), written as inline assembly
  __asm__ __volatile__("dmb ish" ::: "memory");
  __CPROVER_assert(landed, "the write has completed after the barrier");
  return 0;
}
