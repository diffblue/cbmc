volatile int reg;

int main()
{
  // A store to a device register is an observable side effect...
  reg = 0xABCD;
  // ...but a subsequent read may return a different value (the device can
  // change the register), so this must not be provable.
  __CPROVER_assert(reg == 0xABCD, "a volatile read may differ from last write");
  return 0;
}
