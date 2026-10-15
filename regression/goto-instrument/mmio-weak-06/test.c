volatile int reg;

// The device records whether it ever observed the value 1 written to reg.
int saw_one;

void observe(int value)
{
  if(value == 1)
    saw_one = 1;
}

int main()
{
  reg = 1;
  reg = 2;
  // flush all posted writes to the device
  __CPROVER_fence("WWfence", "WRfence", "RWfence", "RRfence");
  __CPROVER_assert(saw_one, "device observed the write of 1");
  return 0;
}
