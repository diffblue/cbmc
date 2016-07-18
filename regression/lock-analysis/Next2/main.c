#include <pthread.h>
#include <stdio.h>

typedef struct S
{
  struct S* next;
  int x;
};

struct S s, t;

int x=0;

void *thread1(void*)
{
  int y=0;
  t.x++;
}

void *thread2(void*)
{
  struct S *ptr=&s;
  ptr=ptr->next;
  ptr->x++;
}


int main()
{
  s.next = &t;

  pthread_t t1;
  pthread_t t2;
  
  pthread_create(
    &t1, 0, thread1, 0);

  pthread_create(
    &t2, 0, thread2, 0);


  return 0;
}
