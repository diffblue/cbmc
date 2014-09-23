void fence() { asm("sync"); }
void lwfence() { asm("lwsync"); }
void isync() { asm("isync"); }

int __unbuffered_cnt=0;
int __unbuffered_p1_EAX=0;
int __unbuffered_p2_EAX=0;
int x=0;
int y=0;
int z=0;

void * P0(void * arg) {
  z = 2;
  x = 1;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

void * P1(void * arg) {
  __unbuffered_p1_EAX = x;
  y = 1;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

void * P2(void * arg) {
  __unbuffered_p2_EAX = y;
  z = 1;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

int main() {
  __CPROVER_ASYNC_0: P0(0);
  __CPROVER_ASYNC_1: P1(0);
  __CPROVER_ASYNC_2: P2(0);
  __CPROVER_assume(__unbuffered_cnt==3);
  fence();
  // EXPECT:exists
  __CPROVER_assert(!(z==2 && __unbuffered_p1_EAX==1 && __unbuffered_p2_EAX==1), "Program was expected to be safe for X86, model checker should have said NO.\nThis likely is a bug in the tool chain.");
  return 0;
}
