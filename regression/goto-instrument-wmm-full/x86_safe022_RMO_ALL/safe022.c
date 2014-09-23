void fence() { asm("sync"); }
void lwfence() { asm("lwsync"); }
void isync() { asm("isync"); }

int __unbuffered_cnt=0;
int __unbuffered_p1_EAX=0;
int __unbuffered_p1_EBX=0;
int x=0;
int y=0;

void * P0(void * arg) {
  y = 1;
  x = 1;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

void * P1(void * arg) {
  __unbuffered_p1_EAX = x;
  __unbuffered_p1_EBX = y;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

int main() {
  __CPROVER_ASYNC_0: P0(0);
  __CPROVER_ASYNC_1: P1(0);
  __CPROVER_assume(__unbuffered_cnt==2);
  fence();
  // EXPECT:exists
  __CPROVER_assert(!(__unbuffered_p1_EAX==1 && __unbuffered_p1_EBX==0), "Program was expected to be safe for X86, model checker should have said NO.\nThis likely is a bug in the tool chain.");
  return 0;
}
