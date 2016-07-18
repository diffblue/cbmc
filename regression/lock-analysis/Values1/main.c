#include <pthread.h>

int i=0;

void *
t1(void* arg)
{
  i=0;
  i=0;

}

void *
t2(void* arg)
{
  i=0;
}


int
main(int argc, char **argv)
{
  int k=0;

  int x=i;

  assert(i<10);

  pthread_t id1, id2;

  pthread_create(&id1, NULL, t1, NULL);
  pthread_create(&id2, NULL, t2, NULL);

}

