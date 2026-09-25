volatile int reg;

int landed;

void observe(int value)
{
  landed = 1;
}

int main()
{
  reg = 1;
  // a completion barrier (ARM DSB): a full fence
  __CPROVER_fence("WWfence", "WRfence", "RWfence", "RRfence");
  __CPROVER_assert(landed, "the write has completed after the barrier");
  return 0;
}
