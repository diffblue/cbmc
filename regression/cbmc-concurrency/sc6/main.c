#include <pthread.h>

volatile unsigned x = 0, y = 0;
volatile unsigned r1 = 0, r2 = 0;

void* thr1(void*) {
  x = 1;
  r1 = y + 1;
}

void* thr2(void*) {
  y = 1;
  r2 = x + 1;
}

int main(){
  pthread_t t1, t2;
  pthread_create(&t1, NULL, thr1, NULL);
  pthread_create(&t2, NULL, thr2, NULL);
  __CPROVER_assert(!(r1 == 1 && r2 == 1), "SC");
  return 0;
}

