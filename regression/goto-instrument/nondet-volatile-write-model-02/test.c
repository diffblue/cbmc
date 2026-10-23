volatile int reg;

// A write model must be a void function; this one returns a value.
int bad(int value)
{
  return value;
}

int main()
{
  reg = 1;
  return 0;
}
