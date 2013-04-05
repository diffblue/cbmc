//#define MUTEX
#ifdef MUTEX
#include <pthread.h>
#endif

//global variables

int x = 0;
#ifdef MUTEX
pthread_mutex_t m;
#else
int m=0;
#endif


void t1() {
#ifdef MUTEX
  int rc = 0;
  rc = pthread_mutex_lock(&m);
  assert(0 == rc);
#else
  __CPROVER_atomic_begin();
  __CPROVER_assume(m==0);
  m=1;
  __CPROVER_atomic_end();
#endif
  x = 7;
#ifdef MUTEX
  pthread_mutex_unlock(&m);
#else
  m=0;
#endif
}

void t2() {
#ifdef MUTEX
  int rc = 0;
  rc = pthread_mutex_lock(&m);
  assert(0 == rc);
#else
  __CPROVER_atomic_begin();
  __CPROVER_assume(m==0);
  m=1;
  __CPROVER_atomic_end();
#endif
  x = 0;
  x += 1;
#ifdef MUTEX
  pthread_mutex_unlock(&m);
#else
  m=0;
#endif
}

void check() {
  assert(x != 8);
}

int main(){
#ifdef MUTEX
  pthread_mutex_init(&m, NULL);
#endif
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();
  __CPROVER_ASYNC_3: check();
  return 0;
}
