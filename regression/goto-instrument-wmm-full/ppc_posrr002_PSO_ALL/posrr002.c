void fence() { asm("sync"); }
void lwfence() { asm("lwsync"); }
void isync() { asm("isync"); }

int __unbuffered_cnt=0;
int __unbuffered_p0_r1=0;
int __unbuffered_p0_r3=0;
int __unbuffered_p1_r1=0;
int __unbuffered_p1_r3=0;
int __unbuffered_p1_r4=0;
int __unbuffered_p1_r6=0;
int __unbuffered_p1_r7=0;
int __unbuffered_p1_r8=0;
int x=0;
int y=0;
int z=0;

void * P0(void * arg) {
  __unbuffered_p0_r1 = 1;
  x = __unbuffered_p0_r1;
  fence();
  __unbuffered_p0_r3 = 1;
  y = __unbuffered_p0_r3;
  // Instrumentation for CPROVER
  fence();
  __unbuffered_cnt++;
}

void * P1(void * arg) {
  __unbuffered_p1_r1 = y;
  __unbuffered_p1_r3 = __unbuffered_p1_r1 ^ __unbuffered_p1_r1;
  __unbuffered_p1_r4 = *(&z + __unbuffered_p1_r3);
  __unbuffered_p1_r6 = z;
  __unbuffered_p1_r7 = __unbuffered_p1_r6 ^ __unbuffered_p1_r6;
  __unbuffered_p1_r8 = *(&x + __unbuffered_p1_r7);
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
  __CPROVER_assert(!(__unbuffered_p1_r1==1 && __unbuffered_p1_r8==0), "Program proven to be relaxed for PPC, model checker says YES.");
  return 0;
}
