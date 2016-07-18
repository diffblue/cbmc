#include <pthread.h>

typedef struct test
{
  int a;
  int b;
} test_t;

typedef struct test2
{
  pthread_mutex_t m;
} test2_t;

void func()
{
  test2_t t;
  test2_t t2;

  t = t2; // +
  pthread_mutex_lock(&(t.m));
}

int main()
{
  pthread_mutex_t m;
  pthread_mutex_lock(&m);
  pthread_mutex_unlock(&m);

  int x;
  int y;
  int z;

  int a[10];
  int i;
  int j;

  void *p;
  test_t t;

  i = 0;
  x = y + *(&z); // +
  x = a[i]; // +
  x = t.a; // +

  p = (void *)&m + t.a; // +
  j = (int)&t; // +
  j = 1; // +

  func();

  return 0;
}

