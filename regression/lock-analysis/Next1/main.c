#include <pthread.h>
#include <stdio.h>

struct S
{
  struct S* next;
  int x;
} s;

struct S *ptr=&s;

int x=0;

void *thread1(void*)
{
  int y=0;

  if(ptr)
    y=ptr->x;
}

void *thread2(void*)
{
  ptr=ptr->next;
}


int main()
{
  ptr=&s;

  pthread_t t1;
  pthread_t t2;
  
  pthread_create(
    &t1, 0, thread1, 0);

  pthread_create(
    &t2, 0, thread2, 0);


  return 0;
}
