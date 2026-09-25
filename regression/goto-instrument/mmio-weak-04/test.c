volatile int A;
volatile int B;

// The device records whether it has observed any write to A.
int a_seen;

void observe_A(int value)
{
  a_seen = 1;
}

void observe_B(int value)
{
  // On the GO command the device requires that a write to A has been observed.
  if(value == 1)
    __CPROVER_assert(a_seen, "a write to A observed before GO");
}

int main()
{
  A = 1;
  A = 2;
  B = 1;
  return 0;
}
