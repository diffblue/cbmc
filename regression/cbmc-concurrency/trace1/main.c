// #include <pthread.h>
#include <assert.h>

volatile unsigned x = 0, y = 0;
volatile unsigned r1 = 0, r2 = 0;

void* thr1(void* arg) {
  x = 1;
  r1 = y + 1;
  return 0;
}

void* thr2(void* arg) {
  y = 1;
  r2 = x + 1;
  return 0;
}

int main(){
  // pthread_t t1, t2;
  // pthread_create(&t1, NULL, thr1, NULL);
  // pthread_create(&t2, NULL, thr2, NULL);
__CPROVER_ASYNC_1: thr1(0);
__CPROVER_ASYNC_2: thr2(0);
  assert(r1 != 1 || r2 != 1);
  return 0;
}

