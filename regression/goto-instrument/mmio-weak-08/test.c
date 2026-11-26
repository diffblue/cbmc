volatile int A;
volatile int B;

int a_seen;

void observe_A(int value)
{
  a_seen = 1;
}

void observe_B(int value)
{
  if(value == 1)
    __CPROVER_assert(a_seen, "A observed before B");
}

int main()
{
  A = 1;
  // an ordering barrier (ARM DMB): a lightweight fence
  __CPROVER_fence("WWfence", "RWfence", "RRfence");
  B = 1;
  return 0;
}
