volatile int reg;

// A device model that observes each write to the register and checks the value
// the driver sends. It must be called with the value written in main (0xAB) and
// not with the compiler's zero-initialisation of the global.
void observe(int value)
{
  __CPROVER_assert(value == 0xAB, "driver writes 0xAB to reg");
}

int main()
{
  reg = 0xAB;
  return 0;
}
