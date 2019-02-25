#ifdef SATABS
#define assert(e) __CPROVER_assert(e,"error")
#endif

volatile int turn; // integer variable to hold the ID of the thread whose turn is it
int x; // variable to test mutual exclusion
volatile int flag1 = 0, flag2 = 0; // boolean flags

void* thr1(void * arg) { // frontend produces 12 transitions from this thread. It would be better if it would produce only 8!
  flag1 = 1;
  turn = 1;
#ifdef __GNUC__
  __asm__ __volatile__ ("mfence": : :"memory");
#else
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
#endif
  __CPROVER_assume(! (flag2==1 && turn==1) );
  // begin: critical section
  x = 0;
  assert(x<=0);
  // end: critical section
  flag1 = 0;
}

void* thr2(void * arg) {
  flag2 = 1;
  turn = 0;
#ifdef __GNUC__
  __asm__ __volatile__ ("mfence": : :"memory");
#else
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
#endif
  __CPROVER_assume(! (flag1==1 && turn==0) );
  // begin: critical section
  x = 1;
  assert (x>=1);
  // end: critical section
  flag2 = 0;
}

int main()
{
  __CPROVER_ASYNC_1: thr1(0);
  thr2(0);
}
