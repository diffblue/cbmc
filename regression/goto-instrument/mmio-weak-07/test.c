volatile int reg;

// The device marks the write as landed when it observes it.
int landed;

void observe(int value)
{
  landed = 1;
}

int main()
{
  reg = 1;
  // an ordering barrier (ARM DMB): a lightweight fence
  __CPROVER_fence("WWfence", "RWfence", "RRfence");
  __CPROVER_assert(landed, "the write has completed after the barrier");
  return 0;
}
