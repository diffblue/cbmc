void fence()
{
  asm("sync");
}
void lwfence()
{
  asm("lwsync");
}
void isync()
{
  asm("isync");
}

int __unbuffered_cnt = 0;
int __unbuffered_p0_EAX = 0;
int __unbuffered_p1_EAX = 0;
int __unbuffered_p1_EBX = 0;
int __unbuffered_p2_EAX = 0;
int __unbuffered_p2_EBX = 0;
int a = 0;
int b = 0;
int x = 0;
int y = 0;
int z = 0;

void *P0(void *arg)
{
  b = 1;
  __unbuffered_p0_EAX = x;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

void *P1(void *arg)
{
  x = 1;
  y = 1;
  __unbuffered_p1_EAX = y;
  __unbuffered_p1_EBX = z;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

void *P2(void *arg)
{
  z = 1;
  a = 1;
  __unbuffered_p2_EAX = a;
  __unbuffered_p2_EBX = b;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

int main()
{
__CPROVER_ASYNC_0:
  P0(0);
__CPROVER_ASYNC_1:
  P1(0);
__CPROVER_ASYNC_2:
  P2(0);
  __CPROVER_assume(__unbuffered_cnt == 3);
  fence();
  // EXPECT:exists
  __CPROVER_assert(
    !(__unbuffered_p0_EAX == 0 && __unbuffered_p1_EAX == 1 &&
      __unbuffered_p1_EBX == 0 && __unbuffered_p2_EAX == 1 &&
      __unbuffered_p2_EBX == 0),
    "Program proven to be relaxed for X86, model checker says YES.");
  return 0;
}
