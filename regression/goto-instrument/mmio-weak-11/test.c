volatile int reg;

int seen;

void observe(int value)
{
  seen = 1;
}

int main()
{
  // three consecutive writes to reg with no intervening barrier: a burst
  reg = 1;
  reg = 2;
  reg = 3;
  return 0;
}
