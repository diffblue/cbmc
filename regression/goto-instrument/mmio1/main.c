volatile int reg;

int main()
{
  // A write to the device register is an observable side effect...
  reg = 7;
  // ...but the device may change the register, so the read-back is
  // non-deterministic and this assertion must not hold.
  __CPROVER_assert(reg == 7, "device may have changed reg");
  return 0;
}
