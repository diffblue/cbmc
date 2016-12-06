#include <pthread.h>

unsigned char nondet_uchar();
unsigned char __CPROVER_uninterpreted_row_hash(unsigned char key);

unsigned char key1, key2, res1, res2, done1, done2;

void *foo1(void *)
{
  res1 = __CPROVER_uninterpreted_row_hash(key1);
  done1 = 1;
}

void *foo2(void *)
{
  res2 = __CPROVER_uninterpreted_row_hash(key2);
  done2 = 1;
}

int main()
{
  key1 = nondet_uchar();
  key2 = key1;

  pthread_t t;
  pthread_create(&t,NULL,foo1,NULL);
  pthread_create(&t,NULL,foo2,NULL);

  if(done1 && done2)
    assert(res1 == res2);
}
